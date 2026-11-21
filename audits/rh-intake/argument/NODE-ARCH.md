# NODE-ARCH: the global objects, as one dictionary

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `PRM` = `Formalism/LocalRingCardinality/Params.lean`
- `SPC` = `Formalism/LocalRingCardinality/DataSpaces.lean`
- `D7F` = `Formalism/LocalRingCardinality/RhoDetPrimeEqMuTildeMulChiPow.lean` (the datum `D7`, lines 76-336)
- `DK` = `Formalism/LocalRingCardinality/DataKernels.lean`
- `ROWS` = `Formalism/LocalRingCardinality/DataRows.lean`
- `DTH` = `Formalism/LocalRingCardinality/DataTheta.lean`
- `DFM` = `Formalism/LocalRingCardinality/DataForms.lean`
- `DDD` = `Formalism/LocalRingCardinality/DataDIVDefs.lean`
- `DH` = `Formalism/LocalRingCardinality/DataHost.lean`
- `IS` = `Formalism/LocalToGlobal/IndefiniteForms/IndefSide.lean`
- `SO` = `Formalism/DivisorInequality/StatementObj.lean`
- `SZ` = `Formalism/HermitianCurvature/StatementSz.lean`
- `PIH` = `Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/PoincareInHH.lean`
- `GA` = `Formalism/SharpRestriction/CuspSpanNormBounds/GlobAut.lean`
- `BT` = `Formalism/LocalToGlobal/IndefiniteReal/BridgeTie.lean`
- `REC` = `Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/StepZeroTwistReferenceTupleEqId.lean`

"The Lean says" means I read the line. *(inferred)* marks my reading. Nothing was compiled. Where I rely on another node's
reading without re-reading the source, I name the node.

## 0. The picture in one paragraph

The proof uses **two towers of hermitian spaces over the host CM field E**. They meet at the top and at the bottom.

- The **column tower** X_0 ⊂ X_1 ⊂ … ⊂ X_m is totally definite, with rank N(j) = k + j(t+1). Its forms are
  algebraic modular forms: vector-valued functions on finite sets of lattice classes. The source forms φ live at level 0.
  The m step maps K_j are Taylor jets of CM theta functions. They push φ up to level m. This is where the p-adic
  divisibility lives.
- The **row tower** Y_m, …, Y_0 has rank r + jt, with r = k + m − 1. Its bottom Y_0 has signature (k + m/2 − 1, m/2) at
  every real place. Its forms are genuine L² automorphic forms. The bottom space EE of the row tower sits inside HH, which
  is the discrete-series, level-(g₀g₁) part of L²(U(Y_0)). Bessel periods for U(X_0) ⊂ U(Y_0) live on HH, and Theorem S is
  proved there.
- **At the top**, Y_m ≅ X′ is the orthogonal complement of an anisotropic vector z in X_m. The period pairing is the
  codimension-one Gross–Prasad period of (level-m column form) × (form on U(X′)).
- **At the bottom**, the identity `BuDef` (with `TieBm`) says: that top period equals the Bessel pairing B_u(φ, ι F),
  where ι is the m-fold descent of the row tower.
- A third family supplies the covolume. The **layers** W_1, …, W_m all have rank r and signatures (k+j−1, m−j). They
  are inner forms of U(Y_0). Each is paired with a definite space V_j of rank r + t. The layer lattices M_j are integral
  cusp forms on the Shimura varieties of U(W_j). The theta maps θ_j : (forms on U(V_j)) → (forms on U(W_j)) have the
  same similitude scalars λ_j as the row descent. That is how covol(RR) becomes a product over the m layers.

So both nodes were right. GLOBALCHAIN describes the column tower, which is definite. THEOREMS describes Y_0, which is
U(k+r_S, r_S+1). VOLUME and COVOL describe the layers W_j.

## 1. The fields and auxiliary primes

| object | definition (Lean) | size | why it is there |
|---|---|---|---|
| K = ℚ(√−d) | `HostRaw.K`; d prime, d ≡ 7 mod 16 (NODE-HOSTS) | log d tiny | CM field of the elliptic curve whose σ*-functions build every theta kernel; "inert in K" is the prime count's (1−χ_d) |
| q | prime, q ≡ 3 mod 8, (−d/q) = 1, q > 4tr+1 (`DH:54`; NODE-HOSTS) | small | second quadratic sign (·/q). It separates **signal** primes (inert in K, split in ℚ(√−q)) from GIdx primes (NODE-SERVED, NODE-SIGNAL) |
| E (host) | abelian CM field, Gal(E/ℚ) = GG = {±1}² × A, \|A\| = n = `ord`; E ⊇ ℚ(√−d, √−q); E ⊂ ℚ(ζ_{QS·q·d}) (NODE-HOSTS; `DH:60-118`) | [E:ℚ] = 4n, n ≍ x^{2+8ε} | all hermitian spaces are over E. Gal(E/ℚ) carries the character ψ under test (the A-coordinate) and indexes the places ρ |
| F = E⁺ | `CMData`, `SPC:14-19` | [F:ℚ] = 2n = f | real places of the unitary groups; f = `Ranks.f` = \|Tau\| = \|Ψ\| |
| Ψ (CM type) | ker of the (−d) sign; `cmType = {ι : ι(√−d) = i√d}`; Ψ = tau1(A) ∪ tau2(A) (`DH:187-190`) | \|Ψ\| = f | the archimedean places τ ∈ Tau ≃ Ψ (`D7F:89`). Split into **tops** tau1(TT), **thick** tau2(dig s + u₀) for s ∈ T2, and **thin** (`DH:131-136`) |
| QS | small conductor, 2^{e+2} \| QS, QS ≤ n² | log QS ≪ x^ε | cuts out the A-part (ψ's 2-power level) |
| g₀, g₁ | two level primes, `DH:71-74` | g ∈ [Y, 2Y], Y = (k e^{x^ε})⁸ (NODE-ORDER) | Bessel/Poincaré level (character χ₂ on the congruence subgroup K₂, `PIH`). They give Theorem S its level savings (2/g)^{(s−1)kf} (NODE-PAIRB). They also carry the depth-zero types that force residual irreducibility (NODE-TWIST) |
| pde, pde′ | two further level primes, ≡ 1 mod 15, ≠ g_i (`DH:76-84`) | — | appear in T_u's congruence and in the Galois-side local set S_i (NODE-CONGMOD). Role not traced further |
| T_u (one per word) | prime, a norm π·π̄ from K with π ≡ 1 mod QS·q·d·(g₀g₁)² (`D7F:144-146`), in [T*, (1+1/(fk))T*] (`D7F:153-154`) | log T ≈ m·x^ε (NODE-ACCOUNT) | the level of the source forms (Mram, below) and the norm −T_u of the Bessel vector z_u |
| ccK, 𝔟 | conductor ideal of the CM curve; half-different (`DH:63-96`) | — | the CM theta function and its p-integrality (NODE-GLOBALCHAIN, Joint.cop) |
| LL | Galois, totally complex number field ⊇ E containing the theta coefficients (`D7F:106-140`) | — | the lattices N_u, RR, M_j are 𝒪_LL-lattices. Its places w carry the valuations |

## 2. Hermitian spaces and groups

All spaces are `HSpace E` (`SPC:26-46`). Each has a hermitian form, a frame, a signature per embedding τ, and a
**unimodular** base lattice L0. The ranks come from `Ranks` (`PRM:6-46`):
- k, m are even and t is odd;
- m + 3 ≤ k, k + m + 4 ≤ t, 3m < t, m ≤ f ≤ k;
- r = k + m − 1, nV = r + t, N(j) = k + j(t+1), rankY(j) = r + jt, rankX′ = r + mt;
- r_S = m/2 − 1, sigY0 = (k + r_S, r_S + 1), sigW(j) = (k + j − 1, m − j).

| space | rank | signature at each real place | Lean | role |
|---|---|---|---|---|
| **X_j**, 0 ≤ j ≤ m (column tower) | N(j) = k + j(t+1) | definite, (N,0) or (0,N) (`X_def`) | `SPC:84-87`; positive definite at j = 0 (`BaseSpacePosDef`, `SPC:153`) | U(X_j) acts on the column forms at level j. X_0 is the definite rank-k space: THEOREMS' W_u |
| **X′** | r + mt = N(m) − 1 | definite (`FactXmDef`, `SPC:155`) | `SPC:89-96`: X′ ↪ X_m isometrically, z ∈ X_m anisotropic, z ⊥ X′ | top period: U(X′) ⊂ U(X_m), codimension 1 |
| **Y_j**, 0 ≤ j ≤ m (row tower) | r + jt | sigYD(j) = (r + jt − ⌊(m−j)/2⌋, ⌊(m−j)/2⌋) (`SPC:75`; `Y_sigval`, `D7F:334`) | `SPC:98-119`: X_j ↪ Y_j isometrically for j < m; Y_m ≅ X′ | U(Y_j) acts on the row forms Mult(j). Y_{m−1} and Y_m are definite. The others are indefinite |
| **Y_0** | r = k + m − 1 | (k + m/2 − 1, m/2) = sigW(m/2) (`PRM:44`, `:82`; `SPC:119`) | Y_0 = X_0 ⊕ ⟨z_m⟩ ⊕ r_S hyperbolic planes; ⟨z_m, z_m⟩ = −T (`SPC:108-117`) | **the** indefinite group of Theorem S: U(k+r_S, r_S+1), non-compact, Witt index r_S ≥ 1 over F |
| **W_j**, 1 ≤ j ≤ m (layers) | r | sigW(j) = (k+j−1, m−j) (`SPC:121-124`) | locally isometric to Y_0 at every finite place (`SPC:126-132`). W_m is positive definite (`FactWmPosDef`, `SPC:160`) | inner forms of U(Y_0). U(W_j) uniformises the layer-j Shimura variety (`ProjectiveLattices/FamilyUniformisationBasePointOrthogonal.lean:423-665`, grep only). For j < m these are positive-dimensional; W_m is the 0-dimensional definite top layer |
| **V_j**, 1 ≤ j ≤ m | nV = r + t | definite (sign `Vneg j`), with orthonormal standard lattice (`SPC:134-139`, `FactVSig` `:157`) | `BT:79-98`: the "L" families of definite forms with weight lamPrime(j) | U(V_j) carries the **type parts**: forms whose parameter contains a Speh-type block, Galois representation of dimension nV = r + t (NODE-LINKN) |

**The Bessel datum** (NODE-THEOREMS, NODE-PAIRB; consistent with `SPC:108-117`). Inside Y_0, take
- the isotropic flag ⟨e_1, …, e_{r_S}⟩ with unipotent radical N;
- for each word u, z_u := c_u^{−1}·z_m with c_u·c̄_u·T_u = T_{u₀} (`zmOf`, `D7F:348`; `cOf_eq`, `D7F:151`), so ⟨z_u, z_u⟩ = −T_u.

The Bessel subgroup is R_u = U(X_0) ⋉ N. Here **W_u = X_0 is the same definite rank-k space for every word.** Words
differ only in the level prime T_u and in the Harish-Chandra parameter u of the source (`hcW`, `D7F:96-102`, which fixes
v, b, e and the first and last u-entries).

**Seesaw diagram** *(the inclusions are in the Lean; the reading as dual pairs is mine)*:

```
 column tower (definite)                   row tower                        layers (covolume side)
 X_m  (rank k+m(t+1))  ⊃  X′ ≅ Y_m  (definite, rank r+mt)                    V_j (definite, r+t) --θ_j--> W_j (r; (k+j−1, m−j))
  ↑K_{m−1}                  ↓ io_{m−1}                                          j = 1..m;  W_m definite;
  ⋮                          ⋮                                                  W_{m/2} ≅ Y_0 at ∞ (same signature)
 X_1  (rank k+t+1)   ⊂     Y_1   (rank r+t)
  ↑K_0                      ↓ io_0
 X_0  (rank k, definite) ⊂ Y_0 (rank r = k+m−1, sig (k+m/2−1, m/2))   ⊃ Bessel subgroup U(X_0)⋉N
```

X_j ⊂ Y_j has codimension m − 1 − j. So the level-j pair is Bessel when that codimension is odd and Fourier–Jacobi
when it is even (`Bper_odd`, DTH:657-664). At level m the inclusion is reversed: Y_m ⊂ X_m, codimension 1 (`Btop`, DTH:665;
`Bm`, DTH:718).

### Reconciling the nodes on "what the groups are"

- **GLOBALCHAIN** ("totally definite groups of rank N(j)") is right **for the column tower** X_j, where the divisibility is
  proved. Its spaces are `sp.X j`, and `Xs_rec` (DTH:642) identifies them with ThetaX's `Xs t j` (rank k + j(t+1), definite,
  DTH:627).
- **THEOREMS** and **VOLUME** ("U(k+r, r+1); definite only for the Bessel subgroup and the top layer") are right **for Y_0**
  (THEOREMS' r is r_S = m/2 − 1, so its n = k + 2r_S + 1 = r) and **for the layers** W_j. "The top layer" means two different
  things: W_m in VOLUME and COVOL, and X_m/X′ in the period map. Both are definite.
- **COVOL**'s "signature (k+i, m−i−1) at layer i+1" is sigW(i+1). The layers are **not** the row-tower spaces Y_j:
  - Y_j has rank r + jt and negative index ⌊(m−j)/2⌋;
  - W_j has rank r and negative index m − j.
  - They coincide in signature only at j = m/2 (Y_0 versus W_{m/2}, `PRM:82`) and at j = m (both definite, of different
    ranks).
- The rank formulas do not conflict. N(j) = k + j(t+1) is the column tower, r + jt is the row tower, and r is every layer.

## 3. Spaces of forms and their lattices

| name (this doc) | Lean | what the forms are | weight | integral structure | metric |
|---|---|---|---|---|---|
| **level-j column forms**, j = 0..m | functions cls j → (Y j → ℂ) (`DK:14-47`); the Hecke-fixed subspace `Fi j` (`DFM:163-165`) | algebraic modular forms on the definite U(X_j): functions on the finite set of classes of lattices in the genus of X_j, valued in the weight representation | `lam j τ` (`DFM:155-159`): the k entries of the source parameter u (which includes the big entry u₀ = a_t + (k−1)/2 at top places τ ∈ TT), then j blocks of t+1 equal entries −wG(e_i), with e_i ≈ cap w_{iτ} | `(fm u).lat j`: Weyl-lattice (Δ) valued, ∇-minor test vectors (NODE-JETA, NODE-ORBIT: `KerEnt.lat_S`) | class-weighted Fischer/Fock form, Σ_c \|stab c\|^{−1}·fock (NODE-HEIGHT: `famIpAt`, `pairK`) |
| **source** Mu0_u ⊇ Mram_u | `ColumnsAtT.Mu0`, `Mram = Mu0 ∩ ⋂_v ker Nm_v` (`DK:126-152`) | level-0 column forms for X_0 (definite, rank k) with level structure at T_u: f copies of 𝔽_{T}, Gauss characters ψ_T. Mram is the part killed by every norm-averaging Nm_v, i.e. the "new / generic at T" part *(inferred)* | lam 0 = the u-vector | **M_u** := (fm u).lat 0; Mram-lattice = `MramL` = comap of M_u (`DDD:12-13`); NuLat_u ⊆ Mram-lattice; **N_u** = I_u·NuLat_u with I_u = ∏_w 𝔭_w^{−⌊e_w·sg(u,w)⌋} (`DDD:15-24`) | the same Fock metric (`nuIn_norm`, `D7F:291-298`; `eMu_isom`) |
| C_u (Poincaré source) | `Cu` (PIH:143) ≅ Mu0 (`s_Cu`, `D7F:233`) | ψ_N-equivariant, χ₂-level functions on the Bessel group R_u = U(X_0) ⋉ N; at ∞ through the Bessel vector W_u of the discrete series | — | — | normalised by c0X (PIH, `Kform`) |
| **HH** | `s.HH`, dim = Dall (`D7F:231`); `HHX`/`RowsAut` (GA:225-261) | L²(U(Y_0)(F)\U(Y_0)(𝔸)): the π_∞-isotypic part (discrete series of U(k+r_S, r_S+1) at each real place, parameter (v, −b) per `Dpar 0`, DTH:538) cut by an admissible idempotent e at level g₀g₁ | Harish-Chandra parameter Dpar 0 = (v_1..v_{k−1}, −b_1..−b_m) | none | Petersson L² |
| **EE** = bottom of the row tower = target ambient | `Rows.EE`, dim Drows = (1−δp)Dall (`ROWS:62-71`); `sEE : EE ↪ HH` isometric (`D7F:307`); `multZero : Mult μ 0 ≅ EE` (`ROWS:96`) | a Dall-dimensional (up to δp ≤ e^{−x^{ez/7}}) subspace of HH, Hecke-isotypically graded by FT | as HH | **RR** ⊂ EE (below) | Petersson |
| **row forms** Mult(μ, j), j = 0..m | `ROWS:92-99`; `rowAF μ j : Mult μ j → cusp(Y_j)` (DTH:675) | cusp forms on U(Y_j). The top is Mult(μ, m) ≅ Amb μ, forms on U(Y_m) ≅ U(X′), definite | Dpar j: (v, −b, j blocks of length t centred at −e_i) (DTH:538-543) | **Mtilde μ** on Amb μ (`ROWS:101`) | petY = mY·Petersson (DTH:726-731), mY a level-index product (`TieMY`) |
| **RR** (target lattice) | `RRDef` (`DDD:26-29`): x ∈ RR iff, at every place w, x is locally in the span of RRset(μ(w)); RRset μ = ι_μ(projection onto Qsp μ of Mtilde μ ∩ V0 μ) (`ROWS:192-199`) | the m-fold descent ι_μ (row tower) of the integral top-level definite forms, projected onto the part not killed by ι, **glued across types μ(w)** place by place | — | 𝒪_LL-lattice in EE (via jEE, `D7F:185`) | Petersson on EE, the dual frame on RR^∨ (NODE-WRITEUP) |
| **type-part spaces** Mt(μ, j) | `ROWS:133-151`; DefSide `Tl j t` (`IS:64`) | definite forms on U(V_j) of rank r+t (the "L" family, `BT:79-98`). Z_j = range(θ_j*) (`ROWS:204`) is the Hecke-eigen type part: theta lifts from U(W_j), with Galois representation ρ ⊕ χ₁ ⊕ … ⊕ χ_t (NODE-LINKN) | lamPrime(j) (`BT:63-75`) | MtLat; **T_j** = projection of MtLat onto Z_j (`TjSet`, `ROWS:206`). Its dual index is the congruence module (NODE-CONGMOD) | Fock/definite (XT_j) |
| **layer lattices M_j**, j = 1..m | `Rows.Mj j`, `MjLat` (`ROWS:123-131`); `IndefData.M j` (`IS:262`) | integral cusp forms of vector weight (kaBig, kaSmall) on the Shimura variety of U(W_j), signature (k+j−1, m−j). Rank D = rank of EE (all layer matrices are D × D in `BoundsMu`, `SO:21-30`) | kaBig : Fin(k+j−1) → ℤ, kaSmall : Fin(m−j) → ℤ per τ | integrality along the special fibres of a model (NODE-COVOL `latW`) | Petersson × (2πx)^{−\|wt\|/2}, probability measure (NODE-COVOL) |
| DN's Mt_i | `DN:150-221` (NODE-CONGMOD) | the Hecke-localised free module of the type-part forms at a residue prime l_i | — | — | — |

**Names that collide.**
- "M" is three objects:
  - M_u = (fm u).lat 0, the source;
  - M_j, the layer cusp-form lattices;
  - Mtilde, the top definite lattice.
- "Mt" is three objects:
  - PeriodMap.Mt ≅ Amb μ₀, the top row forms (`D7F:167`);
  - Rows.Mt μ j, the type parts on U(V_j);
  - DN's Hecke-localised Mt_i.
- "m" is consistent: the number of lifts m = 2r_S + 2 equals Theorem S's 2r + 2 (`SZ:58`).
- "r" is not consistent: Ranks.r = k + m − 1 = rank Y_0, while Theorem S's r is r_S.

## 4. The maps

**(a) The column steps K_j : level j → level j+1** (`DK:63-71`). For φ : cls j → (Y j → ℂ),

  K_jφ(c′) = Σ_{c ∈ cls j} |stab c|^{−1}·ρ_j(c)ρ′_j(c′)·divDe_j ∘ unf_j(c, c′) ∘ sharp_j(φ(c)).

- unf_j(c, c′) is the Taylor jet at 0 of a CM theta function θ_{c,c′} attached to the pair of lattice classes (c, c′). The
  theta function is built from the vacuum of the CM period lattice Λ(δ) (NODE-GLOBALCHAIN `AM/LatAtLattice.lean:73-78`).
- sharp and divDe are diagonal normalisations by the exponents sSharp and sDiv. They differ by (t+1)/2 (`DK:57-61`, `:223-225`).
- ρ, ρ′ are unitary determinant characters, ρ = μ̃_{j+1}^{−1}·χ_D^{−N(j+1)/2} (`D7F:216-221`).
- The chain is col = K_{m−1} ∘ … ∘ K_0 (`DK:70-71`). Twisted chains chTw u μ change only ρ, ρ′ and unf (`DK:79-100`; `D7F:176-183`).
- Direction: **up**, from rank k to rank N(m).
- **Live realisation** (`REC:316-345`):
  - colAF identifies the level-0 forms (`colZero`) and the level-m image col φ (`colTop`) with adelic cusp forms on U(X_0)
    and U(X_m);
  - **for 0 < j < m, colAF is defined to be 0** (`colAF_mid`, `REC:344-345`).
  - So the intermediate column levels are never realised as automorphic forms. They exist only as the algebraic
    class-set functions above.

**(b) The row descent io_j : Mult(j+1) → Mult(j)** (`ROWS:99`).
- It is tied to a genuine theta lift dnY: cusp(Y_{j+1}) → AF(Y_j), with Schwartz datum PhiY and Hecke characters carY
  (DTH:733-735). The tie is adjointness for the Petersson products (`TieIo`, DTH:743-746).
- ι_μ = (descent of all m steps): Amb μ → EE (`ROWS:184-186`). θ_up = ι* (`ROWS:188`).
- Direction: **down**, from rank r + mt to rank r.

**(c) The top period.** PeriodMap: Ptil(ψ, F) = period(lowerMap(evz ψ))(F), and PtilCol φ = Ptil(col φ) (`DK:163-195`).
- `TieBm` (DTH:747-752) reads perCol_u(μ, φ, F) = mY·Btop(X_m ⊃ Y_m)(conj colAF_m φ, rowAF_m F). This is the Gross–Prasad
  restriction period of the level-m column form on U(X_m) against a top row form on U(X′) ≅ U(Y_m).
- `perCol_base_eq_PtilCol` (`D7F:169-171`) identifies it with PtilCol.

**(d) The Bessel pairing.** B_u : Mu_u × EE → ℂ (`ROWS:118`), and on lattices div.Bk u : N_u → RR^∨ (`BuRational`,
`D7F:364`).
- **`BuDef`** (`ROWS:226-227`): for F ∈ V0 μ₀, perCol_u(μ₀, φ, F) = B_u(φ, ι_{μ₀} F).
- **`BesselId`/`L1e`** (`IS:388-397`; GTI:65-67 per NODE-THETA): B_u = a·besS_u up to unitary changes of basis. Here
  besS_u(φ, F) = ⟨sEE F, P_u φ⟩_HH (`D7F:353`).
- P_u : C_u → HH is the Poincaré series Σ_{δ ∈ R_u(F)\G(F)} Ph_T(δx) (PIH:143-216). So P_u^* is the Bessel period map
  HH → C_u^∨.
- `FactBuDetermined` (`ROWS:257-260`): B_u is determined by perCol once ι_{μ₀}(V0) = EE (the HypsAlt field `jOn`).

**(e) The layer maps** (`IS:241-321`). θ_{j,t} : T_j ⊗ K → M_j ⊗ K is a λ_j-similitude from the definite frame XT_j to the
Petersson frame XW_j on each Hecke part (`RowLatticeBoundForBasis`, `IS:304-311`). ι_t is a (κ·∏_j λ_j)-similitude on
the same parts. The scalars λ_j are the Rallis θθ* eigenvalues (NODE-L6). `LevelLink` (`IS:336`) forces the base and
column data to share μ, κ and λ.

**Diagram, with which composite equals which pairing:**

```
           K_0         K_1               K_{m−1}
 N_u ⊆ Mram ⟶ level 1 ⟶ … ⟶ level m  --evz, lowerMap, period-->  (Amb μ0)^∨      [definite; p-adic side]
   │                                                                  ↑ ι^∨  (row descent: io_{m−1}, …, io_0)
   │ B_u  (= a·⟨sEE ·, P_u ·⟩_HH, Bessel period on U(Y_0) ⊃ U(X_0)⋉N)  │
   └─────────────────────────────────────────────────────────────────→ EE^∨ ⊇ RR^∨   [indefinite; archimedean side]

   PtilCol_u(φ)(F) = perCol_u(φ, F) = B_u(φ, ι F)          (BuDef + perCol_base_eq_PtilCol + TieBm)
```

*(inferred)* This is the seesaw iterated m times: "the top period of the m-fold up-lift equals the bottom Bessel period
of the m-fold down-lift". The Lean states it only as the end-to-end identities `TieBm` and `BuDef`. No per-level seesaw
identity is used, consistent with colAF = 0 at middle levels.

## 5. Where each ingredient lives

| ingredient | map | measured in | Lean anchor / node |
|---|---|---|---|
| **p-adic divisibility** | the column chain col = K_{m−1}…K_0 on Mram. The global chain completed at an inert place w equals the local formal-group chain, lattice-exactly | (fm u).lat 0 → ϖ^{gain}·(fm u).lat m ⊗ 𝒪_w, then the period map is integral against Mtilde/RR. The result is v_w⟨F, B_u φ⟩ ≥ ⌊e_w·sg⌋ for φ ∈ NuLat_u, F ∈ RR, i.e. B_u(N_u) ⊆ RR^∨ | `OneMapIntoCC`; NODE-GLOBALCHAIN, CHAININD, ORBIT, SIGNAL. There are two routes: GIdx/Hecke and signal/orbit |
| **archimedean height** | the same factorisation, B_u ≈ PtL ∘ K_{m−1} ∘ … ∘ K_0 divided by the similitude of ι | htMap(B_u) ≤ Σ_j log‖K_j‖² + log‖PtL‖² − log κ − Σ_j log λ_j (Fock norms on the column side, Petersson on EE) | `height_chain_atR` (NODE-HEIGHT); L6 supplies log λ_j ≥ hook − poly |
| **slope inequality** | sources {N_u}_u, target RR^∨, joint map ⊕_u B_u. The frame is Σ_u P_u P_u^* on HH | μ of N_u (Fock), μ(RR^∨) (dual Petersson) | `joint_a_ramified_holds` (NODE-RANK, WRITEUP (5)) |
| **covolume / degree** | RR = glued ι(Pq Mtilde). Its determinant factors as det ι = κ^D·∏_j det θ_j (`SO:31-35`), so μ(RR^∨) ≤ meanLog κ + Σ_j lcv(M_j)/D + index terms (`SO:75-79`) | covolumes of the layer lattices M_j (cusp forms on U(W_j), Petersson). Each is computed by descending through deep covers to the definite W_m, with flat sections giving (p_j − q_j)·logΩ (Chowla–Selberg) | `BoundsMu`; `L3` (`IS:315`); NODE-COVOL, HS, VOLUME |
| **near-orthogonality and dimension count** | P_u : C_u → HH and the Gram kernels P_u^*P_{u′} | dim C_u = d_u ≍ D*/Γ²; dim HH = Dall ≤ (1+η₁)D* | `LinkS_at`; NODE-THEOREMS, PAIRB, COUNT, SLEAVES |
| **congruence modules** | the orthogonal projection onto the type part Z_j ⊂ Mt(μ, j) (forms on U(V_j)). The dual index of T_j = Pr_{Z_j}(MtLat) is at most len(Pr_Z L / L ∩ Z) plus small terms | at twisted places w (μ(w) ≠ μ₀, i.e. resChar ≤ X″ or ∈ {d, g₀, g₁}) | `etaJ_tie` (`D7F:283`); NODE-CONGMOD, LINKN |
| **Selmer bound** | the Galois representations of the type-part eigenforms: ρ_π ⊕ χ₁ ⊕ χ₁ε^{−1} ⊕ … ⊕ χ₁ε^{−(t−1)} over E. The bound is on Bloch–Kato Selmer of ρ⊗χ₁^{−1} (killed by choosing the twist, `KillAt`) and on Ш¹(E, ℚ_l/ℤ_l(−e)) for 0 < e < t | congruence ideal ≤ Selmer (Ribet–Wiles direction) | NODE-CONGMOD, LINKN, ONECHARU, KILLAT, MODU3 |
| **prime count ASK** | Σ over primes p inert in K, odd powers i, of 2 log p·(a_t/p^i − w_{j, partner(t, Frob_p^i)})₊, summed over tops t ∈ TT and lifts j < m. The partner is a place ρ ∈ Φ determined by Frobenius | weights: a_t at top places (the big entry u₀ of the source), caps w = e_j (thick b, top ≈ b′, thin w″) at partner places | NODE-CHBALANCE (FPN:71-87), ACCOUNT |

## 6. A worked count

Sizes are from NODE-ACCOUNT and NODE-PAIRB. The definitions are as read here.
- n ≍ x^{2+8ε}, f = 2n, k ≍ x^{9/2+10ε}, m ≍ x^{1/2−ε/16}.
- t ≍ x^{398.5}, so N(m) = k + m(t+1) ≍ x^{399}, and rank Y_0 = r ≍ k.
- b = e^{x^ε}, a = x·b.

| quantity | formula (Lean) | size |
|---|---|---|
| number of words \|W\| | ⌈3Γ²x^{CF}⌉ (NODE-FAMILY); binary strings of length k, so log\|W\| ≤ (k−3) log 2 | Γ = exp(C m⁵ f x^ε) |
| d_u = dim C_u = dim Mu0_u | vol(U_k)·idxCol·∏_τ dim π_τ·(T_u^k − 1)^f (`ColumnCount`, `SZ:102-103`) | ≍ D*/Γ² (`ChoiceOfT`, `SZ:105-106`); T_u is chosen to hit this window |
| D* | vol(U_n)·idxRow·∏_τ d_{σ_τ} (`SZ:84`), with mass recursion `MassRatios` (`SZ:92-95`) | the limit-multiplicity main term for HH |
| Dall = dim HH | `s_HH` | ≤ (1+η₁)D*, η₁ = e^{−c r f log r} |
| D = dim EE = rank RR | (1−δp)·Dall (`ROWS:71`) | — |
| overfill | Σ_u d_u ≳ \|W\|·D*/Γ² ≈ x^{CF}·D* | the sources overfill the target by about x^{CH} |
| lifts | m. Tops \|TT\| ≥ x^{−ε/8}·n/2; thick T2 with \|T2\|/n = δ ≥ x^{−ε} | — |

**The signal unit.** From NODE-CHBALANCE, `ch_core`:
- For each top t ∈ TT and each lift j < m, the thick partners contribute a Riesz mean of length y = a_t/b ≈ x with
  weight b, namely b·G_ψ(x).
- The proportion of thick partners among Frobenius classes is |T2|/|H| = δ, and the 1/|Φ| normalisation gives a further
  factor ½.
- So U = |TT|·m·b·δ/2 ≈ x^{2.5}·b is (number of top–lift pairs, i.e. Bessel-period relations B_u(φ, ι F) whose
  divisibility is counted) × (cap weight b) × (thick density/2).
- The budget is U·x^{1/2+O(ε)}. It balances x/m against m at m ≈ √x (NODE-ACCOUNT).

*(inferred)* The reading as "number of period relations" uses the fact that each top place t carries one large weight a_t
in the source parameter u, and each lift j adds one block e_j = cap. I did not find a Lean statement naming U this way.
According to NODE-ACCOUNT, GRH:119-122 defines U as above; I did not read that line myself. `BaseSpacePosDef` and
`FactWmPosDef` (`SPC:153`, `:160`) are stated Props. The datum fields that force them are `X_def` and `W_sigval`.

## 7. Points I could not reconcile

1. **The row descent and the layers are linked only through scalars.**
   - The descent ι (Y_m → … → Y_0, ranks r + jt, negative index ⌊(m−j)/2⌋) and the layers (V_j → W_j, rank r,
     negative index m − j) are different towers.
   - The covolume bound needs det ι = κ^D·∏_j det θ_j. This is a hypothesis of `BoundsMu` (`SO:31-35`). It is fed by
     the similitude clauses (`IS:304-311`) and `LevelLink` (`IS:336`).
   - I did not find where the λ_j of the row descent io_j are proved equal to the Rallis scalars of θ_j on U(V_j) ×
     U(W_j). Nor did I find why the layer Shimura varieties have signature (k+j−1, m−j) rather than sigYD(j).
2. **The seesaw is stated end to end, not step by step.**
   - On the live constructor, colAF vanishes at 0 < j < m (`REC:344-345`).
   - `TieBm` and `BuDef` are fields of ThetaX and Rows. I did not trace their proofs (the theta/Siegel–Weil route of
     NODE-THETA is the presumed source).
   - So "the period of the iterated lift is a Bessel period" is an identity I located but did not see proved.
3. **Two d_u's.**
   - Theorem S uses duS u = dim Mu0_u = dim C_u (`D7F:345`; `s_Cu`).
   - The slope chain uses d_u = rk N_u = dim Mram_u ≤ dim Mu0_u (`nuIn_range`, `D7F:293`; `FactDuLe`, `DK:231-233`).
   - Their ratio is not stated anywhere I read. The frame is on P_u restricted to Mram.
4. **Words do not change W_u.** z_u = c_u^{−1}z_m spans the same line for every u (`D7F:348`), so X_0 = W_u for all u.
   NODE-THEOREMS' "each word gives an anisotropic z_u ∈ L_b, a flag and a K-type" must refer to the lattice and flag data
   in the HidaSetting (`HS:216-229` per THEOREMS). I did not check that HidaSetting's V is literally `D.sp.Y 0`.
5. **Mram as "new at T".** My reading of Mram = Mu0 ∩ ⋂ ker Nm_v as the generic/new part at T_u is inferred from
   `FactGaussRam` (`DK:235-239`). I did not confirm it against the Poincaré side's level group.
6. **V_j's role is inferred.** That V_j (rank r + t) carries the type parts comes from the ranks, from `BT:79-98` (the "L"
   families of definite forms on V_j) and from NODE-LINKN's Galois dimension nV. I did not read a statement that θ_j is a
   theta lift between U(V_j) and U(W_j).
7. **The intermediate layers in the Shimura picture.** VOLUME/COVOL's layer j uses deep covers of the same layer-j moduli
   space. Whether the layer index of the M_j tower matches the lift index of K_j one-for-one is supported by
   Σ_j(p_j − q_j) = mk matching m steps of k·w (NODE-ACCOUNT C2). It is not stated as a map between the two towers.

## 8. Coverage

Read in source this pass:
- `PRM:1-140`; `SPC:1-168`; `D7F:1-393` (the whole datum);
- `DK:1-247`; `ROWS:1-274`; `DTH:528-758`; `DFM:107-167`; `DDD:1-40`; `DH:54-145`;
- `IS:1-474`; `SO:1-80`; `SZ:40-150`; `PIH:140-265`; `GA:1-261`;
- `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/Realised.lean:1-129`;
- `Formalism/LocalToGlobal/IndefiniteReal/TopMult.lean:1-140` (adelic glue, not used);
- `BT:55-120`; `REC:300-345`;
- greps for `sp.W`, `sp.V`, `colAF`, `thetaP`.

Nodes read: SUMMARY (all), WRITEUP, FAMILY, GLOBALCHAIN, THEOREMS, PAIRB, COVOL, VOLUME, HEIGHT, L6, CONGMOD, ACCOUNT,
THETA (all); LINKN, CHBALANCE, SIGNAL, ORBIT, HOSTS (§0-1).

Not opened: `DataArith.lean` (B0 and Nc taken from ACCOUNT); the HidaSetting `HS`; `TieBm`/`BuDef`/`TieIo` suppliers;
the rec7 constructor beyond `REC:300-345`; `FamilyUniformisationBasePointOrthogonal.lean` beyond grep lines.
