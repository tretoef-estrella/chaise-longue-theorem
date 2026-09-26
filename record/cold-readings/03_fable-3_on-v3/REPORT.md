VERDICT: HOLDS AS FAR AS I CAN CHECK. I audited the proofs inside [DS] (Theorem 1.1(a), Theorem 2.2 / Lemma 3.3, Claims 4.2–4.3, Theorem 1.4, Corollary 1.5) line by line from the arXiv v3 LaTeX source, re-derived Lemma A.10 and Theorem A.12 by hand, wrote out the §5.8 induction with every quantifier, and recomputed with my own engines (S) at (5,3) = 924 and (6,3) = 3432 with the ballot graded ranks and the ballot-path leading monomials, P3 slice by slice with 0 failures and firing negative controls at (27;3), (27;2), (81;2), (9;4), P1 and (5.1) at seven cells up to (27,4), and P2 at h = 60 exhaustively and h = 200 sampled: no FATAL, no GAP and no ERROR in the paper; every finding is PRESENTATION, plus two slips inside [DS] that do not touch part (a).

# 1. VERDICT
VERDICT: HOLDS AS FAR AS I CAN CHECK. I audited the proofs inside [DS] (Theorem 1.1(a), Theorem 2.2 / Lemma 3.3, Claims 4.2–4.3, Theorem 1.4, Corollary 1.5) line by line from the arXiv v3 LaTeX source, re-derived Lemma A.10 and Theorem A.12 by hand, wrote out the §5.8 induction with every quantifier, and recomputed with my own engines (S) at (5,3) = 924 and (6,3) = 3432 with the ballot graded ranks and the ballot-path leading monomials, P3 slice by slice with 0 failures and firing negative controls at (27;3), (27;2), (81;2), (9;4), P1 and (5.1) at seven cells up to (27,4), and P2 at h = 60 exhaustively and h = 200 sampled: no FATAL, no GAP and no ERROR in the paper; every finding is PRESENTATION, plus two slips inside [DS] that do not touch part (a).

**Summary of the verdict.** The Main Theorem stands on three legs: (1) the [DS] inputs, (2) the translation §2, (3) the combinatorial Theorem 5.3. Legs (2) and (3) had been checked by two referees; I attacked leg (1), which nobody had opened, and the joints of (3) at parameters nobody had reached. Leg (1) holds for every m ≥ 3 and every even n ≥ 2 (Step 1); the n = 0 case is not covered by the [DS] proof but is trivially true (F-3). Leg (3) survives every new test I could afford (Step 2), and its induction is correctly quantified (Step 4). Theorem A's hardest lemma (A.10) and the row inclusions (A.12) are correct (Step 3). I found nothing that a hostile referee could use to reject the paper on mathematical grounds. What remains is the standard residual risk of any 40-page argument audited by three readers and no human expert: I list precisely what I did not check in §4.

# 2. WHAT I CHECKED

## STEP 1 — STATE: CLOSED — Mandate 1: the proofs inside [DS] (arXiv:1405.4683v3, LaTeX source `checks/DS_source/DegtyarevShimada3.tex`)

Numbering check (from the `.tex`, `\newtheorem` shared counter, per section): §1 Thm 1.1 (`thm:main`), Conj 1.2, Def 1.3, Thm 1.4 (`thm:mainrank`), Cor 1.5 (`cor:primem`), Cor 1.6, Cor 1.7; §2 Thm 2.1 (Pham), Thm 2.2 (`thm:LS`, the intersection formula); §3 Rem 3.1, Rem 3.2, Lemma 3.3 (`lem:LambdaW`); §4 Lemma 4.1 (`lem:A`), Claim 4.2 (`claim:LLLKKK`), **Claim 4.3 (`claim:Kp`)**, **Remark 4.4**, **Lemma 4.5** (`lem:phirho`). The paper's citations (1.1(a), 1.3, 1.4, 1.5, 4.3, 4.4, 4.5) all match the arXiv v3 numbering. JMSJ published numbering NOT compared (no access).

### 1.1 What Theorem 1.1(a) actually says and what its proof needs
Statement: Tors_Z(H_n(X)/L_K(X)) ≅ Tors_Z(R/(ψ_J : J ∈ K)). I re-derived the proof (DS §4.2, lines 1304–1478 of the source) line by line. It is an **isomorphism of abelian groups** (in fact of R-modules), not merely an equality of orders. Chain:
(i) H_n(X)/L_K ≅ V_n(X)^∨/L'_K (Claim 4.2, needs P_X ∈ L_K and ker(H_n(X)→V_n(X)^∨) = Z·P_X);
(ii) 0 → V^∨/L' → R/L' → R/V^∨ → 0 with R/V^∨ torsion free ⇒ Tors(V^∨/L') ≅ Tors(R/L') (a group isomorphism: injective obviously, surjective because a torsion element of R/L' maps to 0 in the torsion-free R/V^∨);
(iii) L'_K = (ψ'_J : J∈K) with ψ'_J = ±ψ_J (needs Thm 2.2).
Inputs: (P) Pham: R → H_n(X∖Y_0), 1 ↦ [S], is surjective; (V) V_n(X) := Im(H_n(X∖Y_0)→H_n(X)) is primitive (because H_{n−2}(Y_0) is torsion free); (U) H_n(X) is torsion free with unimodular intersection form and G acts by orientation-preserving maps; (LS) Thm 2.2.

### 1.2 Line-by-line findings in DS §4.2
- **DS's general claim "Im f^∨ = {x : [x,y]=0 ∀y∈Ker f} and Coker f^∨ is torsion free" (lines 1317–1325) is FALSE as stated for a general R-linear f : R → M.** Counterexample: M = R, f = multiplication by 2: Ker f = 0, RHS = R, but Im f^∨ = 2R. The correct statement needs M/Im f torsion free (Hom(M,Z)→Hom(Im f,Z) is onto iff Ext^1(M/Im f, Z)=0 for M free). **In the application f = (R ↠ V_n(X)) is surjective (Pham), so the claim holds there.** Verdict for the paper: harmless (PRESENTATION inside [DS], not a gap).
- Torsion-freeness of R/Im f^∨: if n·x ∈ Ker(f)^⊥ then n[x,y]=0 ⇒ [x,y]=0 (Z-valued form). ✓
- R ≅ R^∨ and H_n(X) ≅ H_n(X)^∨ as R-modules: Φ(gτ)(σ)=⟨gτ,σ⟩=⟨τ,g^{-1}σ⟩=(g·Φ(τ))(σ) with contragredient action. ✓ Needs G-invariance of ⟨,⟩, i.e. G acts orientation-preservingly (holomorphic). ✓
- The formula τ ↦ Σ_ν ⟨τ, γ^ν S⟩ t^ν for the composite H_n(X)→V^∨→R: [x,t^ν] = λ(f(t^ν)) = ⟨τ, γ^ν[S]⟩. ✓
- **Claim 4.2, "by Lefschetz the kernel of H_n(X)↠V_n(X)^∨ is Z·P_X" (line 1369) is terse; I filled it in:** ker = V_n(X)^⊥. rank V_n(X) = rank H_n(X) − 1 because H_n(X)→H_{n−2}(Y_0)≅Z (Lefschetz on Y_0: n−2 < n−1 = dim Y_0) is onto (a standard d-space L meets Y_0={z_0=0} in a (d−1)-plane, the generator). P_X = h^d∩[X] = i_*(h^{d−1}∩[Y_0]) is supported in Y_0, hence ⟂ V_n(X); P_X is primitive because ⟨L, P_X⟩ = deg L = 1. So V^⊥ = Z P_X. ✓ P_X ∈ L_{{J_0}}: X ∩ {z_2=ηz_3,…} = {z_0^m+z_1^m=0} ∩ Λ, reduced union of m standard d-spaces (DS write β_i=η for i≥1 but their plane has z_{2i}=ηz_{2i+1}, i.e. β_i=η^{-1}; irrelevant). ✓
- The G-action [g,J] on B and g^{-1}L_{J,β} = L_{J,[g,J]β}: re-derived (z'_{k_i} = ζ^{ν_{j_i}−ν_{k_i}}β_i z'_{j_i}, ν_0:=0). ✓ Transitivity on B: choose ν_{j_i}=0. ✓
- a_ν = sgn(σ_J) e(ν_{k_0}) Π e(ν_{k_i}−ν_{j_i}); Σ e(ν)t^ν = 1−t; Σ e(ν−ν')t_1^ν t_2^{ν'} = (1−t_1)φ(t_1t_2): re-derived. ✓ Since {k_0, j_i, k_i} = {1..n+1} each t_i is used once ⇒ ψ'_J = ±ψ_J. ✓ (Any J-dependent sign, any t↦t^{-1} convention slip, and the choice (1−t_{k_i}) vs (1−t_{j_i}) all give the same ideal — I checked (1−t_j)φ(t_jt_k) = (unit)(1−t_k)φ(t_jt_k) in R.)

### 1.3 Theorem 2.2 (the intersection numbers) and Lemma 3.3 — the only place where a wrong sign would change the ideal
What matters for (a): (i) ⟨L_{J,β},S⟩ = 0 unless every β_i ∈ {η, η^{-1}}; (ii) then it is ±1; (iii) the sign is s(β_0)·Π s(β_i) up to a sign depending only on d and J. If (iii) failed by a relative sign between β_i=η and β_i=η^{-1} the factor 1−t would become 1+t and the ideal (and Γ_K) would change: I checked that with 1+t at n=2, m=3 the rank formula of Thm 1.4 would give rank L(X)=13 or 20 instead of 7 = ρ(cubic surface). So the sign structure is independently confirmed by known Picard numbers (m=3: 7; m=4: 20 for the Fermat quartic K3 — this also confirms the paper's reading that DS's Remark 4.4 display prints |Γ|, not rank).
Independent re-derivation of Lemma 3.3 (not relying on DS's figure): the intersection points of the perturbed graph Λ̃ = {(z, βz+c)} with W×W are the points w ∈ W ∩ (βW+c), and the local sign is det(T_wW, T_w(βW+c)) (I computed the 4×4 determinant: for lines at angles θ_1,θ_2 it equals Im(β e^{i(θ_1−θ_2)})). So ℓ(β) = planar intersection number of the oriented broken line W (ends at angles +π/m outgoing, −π/m incoming) with βW+c (ends at (2b+2)π/m, 2bπ/m for β=η^{2b+1}); it is +1 / −1 / 0 according as the outgoing end of βW+c lies in the big arc and the incoming in the small arc (b=0, β=η) / the reverse (b=−1, β=η^{-1}) / both in the same arc (all other b). All intersections lie in |z|<ε' (angular separation ≥ π/m), none on the corner {0}, and transversality holds (directions differ by odd multiples of π/m; the antiparallel case β=−1, m odd, gives disjoint parallel rays). Hence ℓ(η)=1, ℓ(η^{-1})=−1, else 0 — exactly s(β). ✓
Local structure of S at p_{k_0}: S = S_{k_0} near p_{k_0} (only γ^νD with ν_{k_0}=0 pass through), D ≅ (−1)^{k_0+1}·orthant (I re-derived the (−1)^{i+1} from the orientation convention (−∂_{s_1},…,−∂_{s_n}) and the Jacobian of eliminating s_{n+1} vs s_i, using n even), Π(1−γ_j^{-1}) turns the orthant into Π W(π/m). ✓ Product formula sign: all factors even-dimensional ⇒ no sign. (−1)^{k_0+1}sgn σ'_J = sgn σ_J (k_0−1 inversions). ✓ The β_0=η^{-1} case is minus the β_0=η case by S = S_{k_0} − γ_{k_0}^{-1}S_{k_0} and γ_{k_0}L_{J,(η^{-1},β')} = L_{J,(η,β')} — rigorous, no local computation needed. ✓
S is a cycle: each face {s_i=0} of D is fixed by γ_i, so (1−γ_i^{-1}) kills it. ✓

### 1.4 Claim 4.3, Theorem 1.4, Corollary 1.5
Re-derived: for p∤m, R⊗K_p is reduced with m^{n+1} points; ψ_J(a)≠0 ⇔ all a_{k_i}≠1 and all a_{j_i}a_{k_i}=1 ⇔ a∈Γ_J (φ(a)=0 ⇔ a≠1 for a∈μ_m, p∤m). dim(A_K⊗K_p) = m^{n+1} − |Γ_K|. Torsion of order p ⇔ dim_{K_p} > dim_C. ✓ Nothing depends on K=𝒥. ✓

### 1.5 Hypotheses for m = 3^v, n = 2k, K = 𝒥
- m > 2 ✓ (m=3 fine). Nothing in §2–§4 uses m prime, or m coprime to anything except in Claim 4.3 (p∤m), which the paper only uses at p=0 and for p∤m.
- **n = 0 (k = 0): the DS proof does NOT cover it.** Pham's theorem as stated (R̄ ≅ H_n(X∖Y_0)) is false for n=0: X∖Y_0 = m points, H_0 = Z^m, while R̄ = Z[t]/(φ) has rank m−1 (the Pham cycle generates only the augmentation-zero part); R → H_0(X) is not surjective, so (P) fails. Also Claim 4.2's Lefschetz argument is vacuous. **But Theorem 1.1(a) is TRUE at n=0 by inspection** (H_0(X)/L(X)=0 and R/(t_1−1)=Z), and the Main Theorem at k=0 is trivial. → PRESENTATION (F-3 below): the paper should say k=0 is trivial instead of routing it through [DS].
- DS define R̄ := R/(φ(t_0),…,φ(t_{n+1})) "=" Z[t_1..t_{n+1}]/(φ(t_1),…,φ(t_{n+1})). **This "=" is false for n+1 ≥ 2**: φ(t_0) is the function m·[Π a_i = 1] on (μ_m∖1)^{n+1}, not zero. Only the right-hand ring is used (Pham, parts (b),(d), §5). Irrelevant to part (a). Noted as a slip in [DS].
- The paper's Remark (2) after Prop 2.5 claims DS §5 prints d_0 = |Γ_K| where it should be (m−1)^{n+1} − |Γ_K|. **Confirmed**: by Lemma 4.5, ρ_J(a) ≠ 0 on (μ_m∖1)^{n+1} iff all a_{j_i}a_{k_i}=1, so V(ρ_J : J∈K) is the complement of Γ_K. DS line 1876 does say d_0 = |Γ_K|. The criterion d_0 = d_p is unaffected. The paper's May-2026 numbers (1124 = 2048 − 924) use the complement reading, consistently.

**Conclusion of Step 1: [DS] Theorem 1.1(a), Claim 4.3, Theorem 1.4 and Corollary 1.5 hold for every m ≥ 3 and every even n ≥ 2, with proofs that are correct after filling in two terse spots (Im f^∨ needs f onto; the kernel Z·P_X). No hidden hypothesis is violated at m = 3^v, K = 𝒥. The case n = 0 is not covered by the DS proof but is trivially true. Nothing FATAL.**

## STEP 2 — STATE: CLOSED (see results below) — Mandates 2, 3 and P2 beyond h = 40: predictions BEFORE running
All code in `checks/`, own design, written from the paper's definitions only.
- **`checks/s_q3.py`** (mandate 3): (S) at q=3 for k=1..6 in C=F_3[y_1..y_{2k+1}]/(y_i^2), generators D_J = Π(y_b−y_a) over the (2k+1)!! matchings, ideal built degree by degree (I_{u+1} = Σ_i y_i I_u), echelon mod 3 with columns in lex order y_1>…>y_{n'}; reads off leading monomials and compares with 𝓤 (ballot paths never below −1). **Predictions:** totals 6, 20, 70, 252, **924**, **3432**; graded ranks (5,3): 132,297,275,154,54,11,1; (6,3): 429,1001,1001,637,273,77,13,1; leading-monomial set = 𝓤 exactly in every degree. Estimate: k=6 has 135 135 generators of 64 terms in a 1716-column space; < 3 min, < 300 MB.
- **`checks/p3_slices.py`** (mandate 2): for (q,m) it enumerates Par_m, all ≼-down-sets Λ, the tight-pattern generators of V_Λ, computes the full ideal V_Λ ⊆ C_m degree by degree with columns ordered by y_1-degree (descending), reads W_j(V_Λ) off the pivots, computes Λ_i from F_Λ (my own implementation of §5.4–5.5), and tests every generator of V_{Λ_i} for membership in W_{q−2−i}(V_Λ). Also reports dim V_Λ vs |Z_Λ| (brute-force enumeration of T^m). **Negative control:** the same test one slice tighter, W_{q−3−i}; it must fail somewhere. **Predictions:** 0 failures of P3 at (27;2), (27;3), (81;2), and for sanity (3;3),(9;3),(9;4); negative control fires at every cell with m ≥ 2 (at least at Λ = {(1)} it must: that is the "no slack" claim); dim V_Λ = |Z_Λ| for every down-set (Remark 5.9(1), measured only); root values 6, 168, 1950 at (3;3),(9;3),(27;3). Estimate (27;3): 17 576-dim ring, ≤ 507 columns per degree, < 2 min, < 200 MB. (81;2): trivial. (27;4) is out of budget (≈10^4 columns per degree), not attempted.
- **`checks/p2_chain.py`**: Prop 5.6 position-wise domination opt_p(μ) ≼ opt_p(μ̃) on all comparable pairs of partitions in Par_m for m ≤ 14 at h = 60 and h = 7 (cap active), and a random sample at h = 200. **Prediction:** 0 failures. < 1 min.

### STEP 2 results (logs in `checks/*.log`)
**Mandate 3 — `checks/s_q3.py` (own engine, lex order y_1>…>y_{n'}):**
| k | dim (D_J)C | prediction Q_k(3) | graded ranks (deg k..n') | = ballot numbers? | LM set = 𝓤 in every degree? | time / peak RSS |
|---|---|---|---|---|---|---|
| 1..4 | 6, 20, 70, 252 | same | as Remark 4.2 | yes | yes | < 1 s |
| **5** | **924** | 924 | 132, 297, 275, 154, 54, 11, 1 | yes | **yes** | 5.5 s |
| **6** | **3432** | 3432 | 429, 1001, 1001, 637, 273, 77, 13, 1 | yes | **yes** | 162 s, **1.45 GB** (over the 1 GB guideline; the 135 135 × 1716 generator matrix) |
The lex leading monomials of the ideal at q=3 are exactly the y_U with U a ballot path never below −1, in every degree, for k ≤ 6 — Theorem 4.1's basis holds where it had never been recomputed. Prediction hit in every number.

**Mandate 2 — `checks/p3_slices.py` (own engine: tight patterns, full ideal degree by degree, W_j read off pivots ordered by y_1-degree, Λ_i from my own implementation of §5.4–5.5, membership of every generator of V_{Λ_i} in W_{q−2−i}):**
| (q, m) | h | #down-sets of Par_m (all) | P3 membership tests | failures | tighter slice W_{q−3−i} (negative control) failures | dim V_Λ = |Z_Λ| | time / RSS |
|---|---|---|---|---|---|---|---|
| (3,3) | 1 | 3 | 10 | 0 | 2 | 3/3 | 0 s |
| (9,3) | 4 | 5 | 90 | 0 | 8 | 5/5 (root 168) | 0.1 s |
| (9,4) | 4 | 10 | 456 | 0 | 61 | 10/10 (0,168,1896,2216,2280,2600,3752,3896,4088,4096) | 35 s / 104 MB |
| **(27,3)** | **13** | 5 | **288** | **0** | **8** | **5/5 (root 1950 = Q_1(27); 15678, 17550, 17576)** | 113 s / 296 MB |
| **(27,2)** | 13 | 4 | 52 | 0 | 2 | 4/4 | 0.2 s |
| **(81,2)** | **40** | 4 | 160 | 0 | 2 | 4/4 | 2 s |
Also checked inside the engine: every layer Λ_i is a ≼-down-set of Par_{m−1} (0 violations); layers that are empty (Λ={∅} at m=2, Λ_i=∅ for i≥1) and layers equal to all of Par_{m−1} (Λ=Par_m) occur and the inclusion holds there too (mandate 5's "empty or full layer" test). The negative control fires at exactly the down-sets where the proof's constructions are tight and does not fire for Λ = Par_m (where V_Λ = C_m and all slices are everything), as it should. The (9,4) values agree with the paper's ten numbers (§8 Gate 2). (27,4) not attempted (≈10^4 columns per degree, out of the 1 GB / 10 min budget).

**P2 beyond h = 40 — `checks/p2_chain.py`:** exhaustive on all comparable pairs of Par_m: h=1 (m≤16), 2 (16), 3 (14), 4 (14), 7 (13), 13 (12), 40 (12), 60 (12): 3795 … 30 496 pairs per row, **0 failures**. A random sample of 600 partitions of size ≤ 30 at h=200 reported 852 failures, but that sample mixed even and odd sizes, i.e. pairs that are NOT both in one Par_{m−1}; Prop 5.6 assumes |μ| ≡ |μ̃| (used in (d1)). Classification by parity (`checks/p2_parity.log`): **0 failures with same parity, 852 with mixed parity.** All 852 are artefacts of my sample (pairs not both in one Par_{m−1}). P2 stands at h = 200 as well.

## STEP 3 — STATE: CLOSED — Mandate 4: Lemma A.10 re-derived by hand
Notation: α_m := [t^m]E_L(t)H_{A;B}(t), β_m := [t^m]E_L(−t)H_{A;B}(t), M = D_L(A,B;c), |A|=|B|=r.
1. E_L(−t)H_{A;B}(t) = E_P(−t)Π_Aφ_a (the B-factors cancel: Π_B(1−bt)·Π_B(1−bt)^{−1}); hence β_M = Θ^c_L(A;B), β_{M−1} = Θ^{c+1}_L(A;B) (D(c+1) = D(c) − 1). ✓
2. E_L(t)H_{A;B}(t) = E_P(t)Π_B(1+bt)/(1−bt); substituting t = −u gives E_P(−u)Π_Bφ_b(u) = E_L(−u)H_{B;A}(u). Since |B| = |A|, D_L(B,A;s) = D_L(A,B;s), so degree M is level c for (B;A) too: α_M = (−1)^MΘ^c_L(B;A). ✓ (This is the only place |A|=|B| is used.)
3. O(t) = ½(E_{L^+}(t) − E_{L^+}(−t)) with E_{L^+}(±t) = E_L(±t)(1±zt) gives X_m := [t^m]O·H = ½(α_m + zα_{m−1} − β_m + zβ_{m−1}). ✓ (char ≠ 2 used here.)
4. Ω := z^ℓX_M − z^{ℓ+1}X_{M−1} = ½z^ℓ(α_M − β_M) + ½z^{ℓ+1}(α_{M−1} + β_{M−1}) − ½z^{ℓ+1}(α_{M−1} − β_{M−1}) − ½z^{ℓ+2}(α_{M−2} + β_{M−2}) = ½z^ℓ(α_M − β_M) + z^{ℓ+1}β_{M−1} − ½z^{ℓ+2}(α_{M−2}+β_{M−2}). ✓ (I expanded it independently; the α_{M−1} terms cancel exactly.)
5. Hence z^{ℓ+1}Θ^{c+1}(A;B) = Ω − ½z^ℓ((−1)^MΘ^c(B;A) − Θ^c(A;B)) + ½z^{ℓ+2}(α_{M−2}+β_{M−2}), and the last term is in z^{ℓ+2}F[L^+]. ✓ Ω = z^ℓΣ_{j odd}e_j(L^+)h_{M−j} − z^{ℓ+1}Σ_{j odd}e_j(L^+)h_{M−1−j} ∈ (e_j(L^+): j odd). ✓
Coefficients α, β, h_m live in F[L] (H is a formal power series with polynomial coefficients); negative indices give 0 by the convention of A.0. **Lemma A.10 is correct.** I also re-derived A.8 (P),(B),(A),(V), A.9, A.13(i)–(iii), Lemma A.6 and every case of Theorem A.12 (lower / value-0 / new-class / raise, including the i* bookkeeping u_{i*} = β_w+1, i* ≤ q−j, u_i − i ≤ β_{w+1} via c_w + c_{w−1} ≤ 2ℓ ≤ q−1): all correct. The one place ½ is used is step 3 (Remark A.16 is right).

**P1 and (5.1) directly — `checks/p1_fibres.py`:** for every down-set Λ and every M' ∈ T^{m−1}, brute-force |F(M')| = #{y ∈ T : λ(y,M') ∈ Λ} against F_Λ(λ(M')) (option count) and against formula (5.1) (r, N, j_0 computed independently): (3,4), (3,6), (9,3), (9,4), (9,5), (27,3), (27,4): 238 257 tests, **0 failures** (log `checks/p1_fibres.log`).

## STEP 4 — STATE: CLOSED — Mandate 5: the induction of §5.8 with every quantifier
**Statement P(m), q = 3^v fixed once and for all, h = (q−1)/2:** for every subset Λ ⊆ Par_m = {λ : |λ| ≤ m, |λ| ≡ m (2), ℓ(λ) ≤ h} which is a down-set for ≼ *restricted to Par_m* (λ ∈ Λ, λ' ∈ Par_m, λ' ≼ λ ⇒ λ' ∈ Λ), and for every ring C_m = F_3[y_{a_1},…,y_{a_m}]/(y^{q−1}) on any m-element index set, dim V_Λ ≥ |Z_Λ|.
Invariance under relabelling: a permutation of the index set sends each tight-pattern product to ± another one (D and Δ are antisymmetric), so V_Λ is permutation-invariant and Z_Λ obviously is. (The paper asserts this in one clause; the ± is the whole content.)
**Base P(0):** Par_0 = {∅}; Λ = {∅}: V = C_0 = F_3 (empty product), Z = T^0 = one point; Λ = ∅: 0 ≥ 0. ✓
**Step P(m−1) ⇒ P(m), m ≥ 1.** Given a down-set Λ ⊆ Par_m, for i = 0,…,q−2 define Λ_i := {μ ∈ Par_{m−1} : F_Λ(μ) > i}, with F_Λ(μ) = #{j ≤ ℓ(μ): μ−e_j ∈ Λ} + #{j : μ+e_j ∈ Λ} + (q−1−2ℓ(μ))[μ⊔1 ∈ Λ] (when ℓ = h the last term is 0 both because the factor is 0 and because μ⊔1 ∉ Par_m). The four facts used, each with the hypothesis it needs:
(a) Every option of μ ∈ Par_{m−1} lies in Par_m (parity flips, size ≤ m, length ≤ h since μ⊔1 only when ℓ<h). Needs only μ ∈ Par_{m−1}. — So |F(M')| = F_Λ(λ(M')) for M' ∈ T^{m−1} (P1), hence Z_{>i} = Z_{Λ_i} and, by Lemma 5.1(iv), |Z_Λ| = Σ_{i=0}^{q−2} |Z_{Λ_i}|.
(b) Λ_i is a ≼-down-set of Par_{m−1} (Prop 5.6). Needs: Λ a down-set; μ, μ̃ ∈ Par_{m−1} (same parity, used in (d1); ℓ,ℓ̃ ≤ h, used in (e1) and in ℓ+ℓ̃ ≤ L).
(c) V_{Λ_i} ⊆ W_{q−2−i}(V_Λ) (Prop 5.8). Needs: Λ a down-set (Lemma 5.5 ⇒ the options in Λ are an initial segment ⇒ (5.1)); ℓ(μ) ≤ h (so |B| ≤ h−1 ≤ q−2 and y_1^{|B|} ≠ 0); |μ| ≡ m−1 (so the pair counts are integers).
(d) dim V_Λ = Σ_j dim W_j(V_Λ) (Lemma 5.1(iii); needs V_Λ = V_{≤q−2}, true since exponents < q−1).
Then dim V_Λ = Σ_i dim W_{q−2−i}(V_Λ) ≥ Σ_i dim V_{Λ_i} ≥ Σ_i |Z_{Λ_i}| = |Z_Λ|, where the middle inequality is P(m−1) applied to each Λ_i on the index set {2,…,m}. Λ_i ⊆ Par_{m−1} by definition and is a down-set by (b), so the hypothesis applied is exactly the one assumed. Nothing depends on Λ containing any particular partition; Λ = ∅ (all Λ_i = ∅, V = 0, Z = ∅) and Λ = Par_m (all Λ_i = Par_{m−1}, V = C_m because (m) ∈ Par_m has product 1) are legitimate instances and the step is trivially true for them; intermediate Λ with empty layers (Λ = {∅} at m = 2: Λ_i = ∅ for i ≥ 1) and with full layers (Λ = {∅} at m = 2: Λ_0 = Par_1) occur and were tested by `p3_slices.py` (0 failures). The case m = 1 (peeling the only variable, C_0 = F_3) was checked by hand: Λ = {(1)} gives V = C_1, F_Λ(∅) = q−1, Λ_i = {∅} for all i, W_j(C_1) = F_3 ⊇ V_{{∅}} = F_3. ✓
**Verdict: the induction is sound; its quantifiers are as the paper implies, and q is fixed throughout.** The one thing worth adding in print is the relabelling remark (one line) and that q is fixed in the induction (the theorem statement quantifies over q too, which is harmless).

## STEP 5 — STATE: CLOSED — Mandate 6: sentences asserted without proof, with one-line proofs
(I compiled the list myself; none is false.)
1. §2.1 "R is a free Z-module of rank m^{n+1}" — basis t^ν, ν ∈ (Z/m)^{n+1}.
2. "dim_{F_p}(A ⊗ F_p) = ρ + c_p" — (Z^ρ ⊕ ⊕_ℓ T_ℓ) ⊗ F_p = F_p^ρ ⊕ T_p ⊗ F_p and Z/p^a ⊗ F_p = F_p, Z/ℓ^a ⊗ F_p = 0 (ℓ≠p). Right exactness is not even needed, only additivity.
3. Lemma 2.3(i) "spanned by 1, y, …, y^{q−1}" — y = (t−1)u with u a unit, so y^j = (t−1)^j u^j ≠ 0 for j ≤ q−1 and y^q = t^q − t^{−q} = 0; q independent elements in a q-dimensional ring.
4. Prop 2.6 "the pairing is non-degenerate" — ⟨y^α, y^β⟩ = [α+β = (q−1,…,q−1)] is a permutation matrix. "f ∈ ann(I) iff f ⊥ I" — ⟨f, gh⟩ = ⟨fg, h⟩ and non-degeneracy. "annihilator of a monomial in the box ring" — ann(y^a) = (y_i^{q−a_i}) (monomial ideal, exponent by exponent).
5. Prop 2.6 "ℓ^q = Σ c_i y_i^q" — Frobenius and c^q = c for c ∈ F_3 (more generally F_p).
6. §3 "Q_k(3) = C(2k+2,k+1)" — [x^{2k+2}] I_0(2x) = 1/((k+1)!)^2.
7. Theorem 4.1(iv) "elements with distinct leading monomials are independent" — the leading monomial of a non-trivial combination is the largest leading monomial with non-zero coefficient.
8. Theorem 4.1(iii) reflection — André's reflection at the first visit to −2 maps paths visiting −2 with u up-steps bijectively onto paths with n'−u−2 up-steps.
9. Prop 7.1 "an ideal and its initial ideal have the same colength" — Macaulay [CLO]; "in(I∩J) ⊆ in(I) ∩ in(J)" — I∩J ⊆ I and I∩J ⊆ J; "the ideal of V(I_J) ∩ T^N is I_J + (x_i^{q−1} − 1)" — mod I_J one free variable per pair, and x^{q−1} − 1 is separable with roots exactly T; "its initial ideal equals I_J + (x_i^{q−1})" — containment plus equal colength (q−1)^{k+1}.
10. §1.3 / §7.1 "a point lies on ∪V(I_J) iff its multiset of coordinates is closed under negation iff Π(1+x_it) is even" — Π(1+x_it) = Π(1−x_it) ⇔ equality of multisets {x_i} = {−x_i} (unique factorisation in F̄[t]); an even number of zeros then pairs with itself, and an odd number is impossible since N is even and the non-zero values pair up.
11. §5.2 "ν(M) = Σ_classes min(a,ā)" — a negation pair lies inside one class and classes are disjoint. "|λ(M)| = m − 2ν(M)" — Σ|a−ā| = Σ(a+ā) − 2Σmin.
12. Lemma 5.7(ii) — Laplace expansion along the last row of the Vandermonde matrix; two equal rows for t ≤ r−2.
13. Lemma A.6 — checked (Step 3). Lemma A.4/A.1 — checked.
14. §5.8 "the statement is invariant under relabelling" — see Step 4 (needs the ± of D and Δ).
15. DS 1.1(a) "isomorphic torsions" as used in Prop 2.1 ("torsion free iff torsion free") — Step 1.
The one sentence I would call *not* standard and *not* proved but harmless: §2.1 "By Theorem 1.1(a), H_n(X)/L_K(X) is torsion free iff A_K is" — at k = 0 this rests on a statement whose proof in [DS] does not cover n = 0 (F-3).

## STEP 6 — STATE: CLOSED — Mandate 7: hostile read from line 1; every place I had to trust the authors
Trusted and NOT independently verified by me: (i) Pham 1965 (surjectivity of R → H_n(affine Fermat)) and torsion-freeness of H_*(smooth hypersurface) — classical; (ii) [De14], [De15] contents; (iii) the repository and all of §8's history (forbidden to open); (iv) Fact 7.2 (4730 < 4736) and the "800 of 32 767 subfamilies" count (not used in any proof); (v) the (2,9), (1,27) graded-rank tables of §8 except the totals 1950 (mine) and 168 (mine); (vi) Remarks 4.2(3), 5.9(2), 6.3(2) (not used); (vii) Theorem A's numerics (Route 6). Everything else in §1–§7 and Appendix A I re-derived or recomputed.
Places where a hostile expert stops (all resolved):
- §1.2 rank clause uses Thm 1.4 (previous referees). — PRESENTATION, already listed.
- §2 first bullet "t_0 never enters below" — true; DS's ψ_J is in t_1..t_{n+1} only.
- Prop 2.1 at p ∤ m: uses Claim 4.3 for p ∤ m *and* Cor 1.5; either suffices.
- Lemma 2.4(ii) sign ± and unit: irrelevant for an ideal; but the paper should say "unit of B", which it does.
- Prop 2.5 "and it suffices to prove ≥": correct since ≤ is proved.
- §3 table: I recomputed 1950, 234 260, 190 120, 37 849 630 from the polynomials of Remark 4.4 and 1950/168/6 by point enumeration. ✓
- Theorem 4.1: proof read line by line; (i)–(iv) hold; recomputed through k = 6 (Step 2). ✓
- §5.4–5.8: re-derived (Steps 2, 4); numerics (Step 2). ✓
- Prop 7.1 both inequalities re-derived (item 9 above). ✓
- §8 "(6,3), never computed before" vs "What went wrong" paragraph — internal history only.
- Appendix A re-derived (Step 3). ✓

# 3. FINDINGS

Classification: FATAL / GAP / ERROR / PRESENTATION. **There is no FATAL, no GAP and no ERROR in the paper.** Items already listed by the previous referees are not repeated.

**F-1 · PRESENTATION (inside [DS], harmless to the paper).** [DS] §4.2, source lines 1317–1325: "the image of the dual homomorphism f^∨ … is Im f^∨ = {x ∈ R : [x,y] = 0 for any y ∈ Ker f}, and the cokernel of f^∨ is always torsion free" is asserted for an arbitrary R-linear f : R → M. **False in that generality**: M = R, f = 2·id gives Ker f = 0, the right-hand side R, but Im f^∨ = 2R. It is true when M/Im f is torsion free, and in [DS] it is applied only to the surjection R ↠ V_n(X) of Pham's theorem. Exact missing step: "f is onto, so Hom(M,Z) → Hom(Im f,Z) is the identity". The paper's proof is unaffected, but a referee reading [DS] §4.2 for the first time will stop here; see §5, item (a).

**F-2 · ERROR (inside [DS], irrelevant to the paper).** [DS] §1, source line 341: R̄ := R/(φ(t_0), …, φ(t_{n+1})) "=" Z[t_1,…,t_{n+1}]/(φ(t_1),…,φ(t_{n+1})). For n+1 ≥ 2 the two rings differ: over C the first kills the (m−1)^{n+1}-point set at the points with Π a_i = 1 (φ(t_0) is the function m·[Π a_i = 1]), the second does not. Pham's theorem (rank (m−1)^{n+1}) needs the second ring, which is the one [DS] actually use in parts (b), (d) and §5. The paper cites only part (a) and, in §8, the correct ring F_3[t]/(φ(t_i)). No effect.

**F-3 · PRESENTATION (paper, Main Theorem "k ≥ 0" and §2).** The paper routes k = 0 through [DS, Theorem 1.1(a)], whose proof in [DS] assumes n ≥ 2: for n = 0 Pham's theorem as stated is false (X∖Y_0 is m points, H_0 = Z^m, but R̄ has rank m−1; the Pham cycle generates only the augmentation-zero part, so R → H_0(X) is not onto and the dual-ideal argument does not start), and Claim 4.2's Lefschetz argument is empty. The statement of 1.1(a) at n = 0 is nevertheless true by inspection (H_0(X)/L(X) = 0; R/(t_1−1) = Z), so the Main Theorem at k = 0 holds — trivially, since L(X) = H_0(X). Exact fix: one sentence "For k = 0 the Main Theorem is trivial (L(X) = H_0(X) = Z^m); from now on k ≥ 1", and the same caveat in the "three results of [DS]" list.

**F-4 · PRESENTATION (paper, §5.8, last sentence of the proof).** "The statement is invariant under relabelling the indices" is used to apply the induction hypothesis on {2,…,m}. The one-line reason is missing: a permutation of the index set maps every tight-pattern product to ± another one (D and Δ are antisymmetric), so V_Λ is permutation-invariant. Also say explicitly that q is fixed throughout the induction (Theorem 5.3 quantifies over q, the induction does not).

**F-5 · PRESENTATION (paper, §2, external check after Lemma 2.2).** The paper's reading of [DS, Remark 4.4] ("the display drops the 1") is right, but the cleanest evidence is not printed: at m = 3 the display gives 6 and rank L(X) = 7 = ρ(cubic surface), at m = 4 it gives 19 and rank L(X) = 20 = ρ(Fermat quartic K3). This also independently confirms the sign structure of [DS, Theorem 2.2] (with 1+t in place of 1−t the rank would be 13 or 20 at m = 3). Worth one line: it is the only check of the translation that does not pass through [DS].

**F-6 · PRESENTATION (paper, Remark 5.9(1) and §10 "MEASURED, NOT CLAIMED").** The reverse inequality dim V_Λ ≤ |Z_Λ| is not only measurable, it is provable in ten lines from ingredients already in the paper (Prop 7.1's degeneration plus the evaluation of D and Δ on T^m plus Gale–Ryser); see §5 item (e). Not a defect — an opportunity.

**F-7 · PRESENTATION (paper, §8 Route 1 vs §10).** §8 says the (6,3) run took 489 MB; my independent engine needed 1.45 GB for the same cell (different design). Not a finding against the paper; recorded so that nobody thinks the two numbers should agree.

**Inside [DS], also noted (no classification needed):** in the proof of Claim 4.2 the plane is written z_{2i} − ηz_{2i+1} = 0 while the spaces are labelled with β_i = η (they have β_i = η^{-1}); the proof of Claim 4.2's kernel statement ("by the Lefschetz hyperplane section theorem") is two lines of work in reality (Step 1.2); [DS] §5 prints d_0 = |Γ_K| for what is (m−1)^{n+1} − |Γ_K| (the paper already says so, correctly).

# 4. WHAT I DID NOT CHECK

- **The published JMSJ version of [DS]**: numbering and text not compared (no access). All citations were checked against arXiv v3.
- **Pham's theorem** (surjectivity of Z[G] → H_n(affine Fermat), 1 ↦ [S]) and **torsion-freeness of H_*(smooth hypersurface)**: taken as classical; not re-proved.
- **[DS] Lemma 3.3's own 4×4 determinants and figure**: I replaced them by an independent argument (planar linking of the two broken lines) that fixes the relative signs and the vanishing; I did not verify [DS]'s literal sign conventions (a global sign is irrelevant to part (a)).
- **[DS] parts (b), (c), (d) of Theorem 1.1 and Corollaries 1.6–1.7**: read, not audited (the paper does not use them).
- **The seven cases of Prop 5.6 by hand**: done by both previous referees; I only tested them numerically (exhaustive to h = 60, m ≤ 12; sampled at h = 200, 97 190 comparable pairs).
- **(S) at q ≥ 9 beyond m = 3**: I did not recompute (2,9) = 5120, (3,9) = 190 120 or (1,27)'s graded ranks (only its total 1950, via Theorem 5.3's root at (27,3)). **(27,4)** and **(81,3)** for P3 are out of the 1 GB / 10 min budget.
- **Fact 7.2** (4730 < 4736) and the "800 of 32 767 subfamilies" count: not recomputed (used in no proof).
- **Theorem A numerics** (Route 6) and **Prop A.5** beyond a careful reading: not recomputed.
- **Remarks 4.2(3), 5.9(2), 6.3(2)** (Specht, Cerlienco–Mureddu, Steinberg): not checked; not used.
- **[De14], [De15]** and every historical statement of §1.4, §8, §9: not checked; the repository was not opened, as instructed.
- **Independence of my engines from the authors'**: I never saw their code; my code is in `checks/` (about 400 lines) and was written from the paper's definitions only. Bugs I found and fixed in my own code before any result was recorded: `pairsets` paired the first index always (partial matchings need a choice of the paired subset), and the h = 200 P2 sample mixed parities (Step 2).

# 5. HOW TO MAKE THE PAPER MORE ROBUST AND BRILLIANT

The previous referees asked for: a one-page algebraic statement; the [DS] inputs as one theorem; worked examples at (1,3) and (1,9); a figure of the chain; a table of the seven cases; the narrative moved to a supplement. My position on each, then what they did not think of.

**Agree, with a sharpening.**
- *The [DS] inputs as one theorem* — yes, but **with a self-contained proof of part (a) modulo Pham and Theorem 2.2** (half a page). Reason: [DS] §4.2 contains a false general lemma (F-1) and a two-line Lefschetz claim that takes real work (Step 1.2); a hostile referee will go to [DS], stumble, and blame the paper. The proof to print: (1) R ↠ V_n(X) (Pham + primitivity of V_n(X) since H_{n−2}(Y_0) is torsion free); (2) for a *surjection* f : R ↠ M of R-modules, f^∨ identifies M^∨ with the ideal Ker(f)^⊥ ⊆ R ≅ R^∨ and R/Ker(f)^⊥ is torsion free; (3) H_n(X) ≅ H_n(X)^∨ → V_n(X)^∨ is onto with kernel V_n(X)^⊥ = Z·P_X (rank count via H_n(X) ↠ H_{n−2}(Y_0) ≅ Z and primitivity of P_X from ⟨L, P_X⟩ = 1), and P_X ∈ L_{{J}}(X) for every J; (4) L_K(X) = Σ_J R·[L_{J,(η,…,η)}] and its image in R is (ψ_J) by Theorem 2.2; (5) the torsion transfer through 0 → V^∨/L' → R/L' → R/V^∨ → 0. Everything in Step 1 of this report can be lifted.
- *One-page algebraic statement* — yes: "Theorem. For q = 3^v, k ≥ 0: dim_{F_3}(D_J : J ∈ 𝒥)C = Q_k(q)", followed by "Theorem 5.3" and "Proposition 2.5", in that order, before any topology.
- *Figure of the chain, table of the seven cases* — yes.
- *Worked examples* — **partly disagree.** (1,3) and (1,9) illustrate §2–§4, not §5: at q = 3 there are no middle options (h = 1) and at m = 3 the poset Par_3 is a chain. The example that teaches §5 is **(q,m) = (9,4)**: Par_4 has 8 elements and 10 down-sets, the layer sizes vary (my log `checks/p3_9_4.log` prints them), and all three constructions (α), (β), (γ) of Prop 5.8 occur. Print (1,3) for §2 and (9,4) for §5.
- *Narrative to a supplement* — **agree for §8 (routes), §9 and the title-block prose; disagree for §1.4 and §7.** §7 is mathematics a referee needs (the sandwich and the subfamily counterexample are the reason the proof must use the full family), and the two-paragraph history of the false identification A = P in §1.4 is what makes §7 credible. Keep both, shorten §1.4 to five lines.

**What they did not think of.**
- **(a) State Theorem 5.3 over an arbitrary field and an arbitrary odd q.** Nothing in §5 uses F_3 or q = 3^v: Lemma 5.7 is over Z, the peeling is over any field, and T is any set of size q−1 with a fixed-point-free involution. Printed as "Theorem 5.3′ (any field F, any odd q ≥ 3, any ≼-down-set Λ ⊆ Par_m^{(h)}): dim_F V_Λ ≥ |Z_Λ|", the theorem becomes visibly independent of the arithmetic, the p ≥ 5 case becomes a corollary of a rewritten §2 (see §6), and the paper gains a purely combinatorial theorem of independent interest.
- **(b) Say k = 0 is trivial** (F-3) and start the proof at k ≥ 1.
- **(c) Add the Picard-number line** (F-5) after the external check of Lemma 2.2.
- **(d) Make the ≤ direction visibly independent of [DS]**: Prop 7.1 (left inequality) plus Prop 2.6 already give dim(D_J)C ≤ Q_k(q) by pure algebra. Say so in one sentence in §2: then [DS] is needed only for "torsion free ⇔ equality" and for the rank, and the reader sees exactly what topology buys.
- **(e) Prove the equality in Theorem 5.3** (F-6). Sketch, all ingredients already in the paper: over F_q, let Fun := F_q[y]/(y_i^{q−1} − 1) = functions on T^m. On T^m, D(y_a,y_b) is supported exactly on {y_b = −y_a} (it equals y_a^{q−2} there and 0 elsewhere since y^{q−1} = 1), and Δ(B) is non-zero exactly where the values on B are distinct. So a tight-pattern product of λ is non-zero at M iff its p pairs are negation pairs of M and the remaining |λ| entries fill the columns of λ with distinct values per column, which by Gale–Ryser means: the multiplicity partition ν' of M minus those p pairs satisfies ν' ≼ λ. Since removing further negation pairs only lowers partial sums, λ(M) ≼ ν' ≼ λ; conversely λ = λ(M) with the maximal pairs works. Hence {M : some generator of V_Λ is non-zero at M} = Z_Λ for a down-set Λ. Then the degeneration of Prop 7.1 (the initial ideal of (generators) + (y_i^{q−1} − 1) contains (generators) + (y_i^{q−1}); Macaulay) gives dim V_Λ ≤ dim (generators)·Fun = |Z_Λ|. With Theorem 5.3 this is **dim_F V_Λ = |Z_Λ| for every down-set** — a clean statement, and the "MEASURED, NOT CLAIMED" line of §10 disappears. (This is my sketch; it has not been audited by anyone else and the paper does not depend on it.)
- **(f) Write Par_m as Par_m^{(h)}** — the dependence on h is what makes Prop 5.6's cases (e1)–(e2) and the μ⊔1 bookkeeping exist; a reader who forgets it will think (1^m) ∈ Par_m always.
- **(g) In §5.5, print the chain with its positions once as a picture** (removals μ−e_1 … μ−e_ℓ | q−1−2ℓ copies of μ⊔1 | μ+e_ℓ … μ+e_1), and in (5.1) rename N to avoid the clash with N = 2k+2 (previous referees).
- **(h) The record of negative controls should be in the main text, one line each** ("tightening P3 by one slice fails 604 times at (9,7)"): it is what distinguishes a proof that was tested from one that was only checked.
- **(i) Title block and authorship prose** ("Written and audited by Grepy…", the campaign vocabulary) belong in the supplement or the acknowledgements; a journal will not print them as they stand, and they distract from a result that does not need them.
- **(j) In the citation of [DS] §5 write R̄ := F_3[t_1,…,t_{2k+1}]/(φ(t_i))** explicitly (F-2), so that nobody re-derives [DS]'s "=" and stops.

# 6. OPINION: HOW TO PROVE THE CASE p ≥ 5

**Instruction: first try to prove the previous referees wrong** (they believe the paper already proves m = p^v for every odd prime p).

**Adversarial search for a hidden 3.** I listed every occurrence of "3", "F_3", "characteristic 3" and "q = 3^v" in §2 and §5 and asked, for each, what the argument needs:
- Lemma 2.3(i): t^q − 1 = (t−1)^q — needs char p and q = p^v (Frobenius), not 3. y = t^{-1}(t−1)(t+1) with t + 1 = 2 + (t−1) a unit — needs 2 ∈ F_p^× only. y^q = t^q − t^{−q} = 0 — Frobenius. Dimension count q — any p.
- Lemma 2.3(ii): t_j + t_k = 2 + (t_j−1) + (t_k−1) a unit — needs 2 ∈ F_p^×.
- Lemma 2.3(iii): (u−1)φ(u) = u^q − 1 = (u−1)^q — Frobenius.
- D(a,b) = (b^{q−1} − a^{q−1})/(a+b) — q−2 odd, any odd q. Antisymmetry — none.
- Lemma 2.4(i): (a+b)·Σ(−1)^s a^s b^{q−1−s} = a^q + b^q = (a+b)^q — the telescoping uses q−1 even; the last equality is Frobenius in char p. I re-did the telescoping: the cross terms cancel pairwise for any q, leaving (−1)^{q−1}a^q + b^q.
- Lemma 2.4(ii), Prop 2.5: units, monomials, dimension counts — none.
- Prop 2.6: ℓ^q = Σ c_i y_i^q for c_i ∈ F_p — c^q = c and Frobenius.
- Lemma 2.2 / Lemma 3.1: q odd (inversion fixed-point-free on μ_q∖{1}) — any odd q.
- §5 entirely: the identities of Lemma 5.7 hold over Z; the peeling (Lemma 5.1) holds over any field; T is used only as a set with a fixed-point-free involution and h = (q−1)/2 classes; the bounds |B| ≤ h−1 ≤ q−2, r ≥ 1 ⇒ q−1−r ≤ q−2 hold for every odd q ≥ 3; Prop 5.6 uses ℓ+ℓ̃ ≤ 2h = q−1 and parity, both parameter-free.
- [DS] inputs: Theorem 1.1(a) and Claim 4.3 for every m ≥ 3 (Step 1); Corollary 1.5 says only p | m can occur, so for m = p^v only p matters.
**Result: I could not find a hidden 3. The previous referees are right.** The two arithmetic facts used are (F) (u+w)^q = u^q + w^q in characteristic p for q = p^v, and (U) 2 ∈ F_p^×. Both hold for every odd prime p. (Where 2 fails, p = 2, everything in §2 collapses at once: t+1 is not a unit and there is no antisymmetric coordinate.)

**The rewritten §2 for a general odd prime p, sentence by sentence (draft).**
*Conventions.* Let p be an odd prime, v ≥ 1, q = m = p^v, N = 2k+2, T = F_q^×, h = (q−1)/2. All dimensions are over F_p.
*Prop 2.1.* Unchanged (it holds for every m and every prime).
*After Prop 2.1.* "For m = q = p^v only the prime p matters, and A_K ⊗ F_p = F_p[G]/(ψ̄_J : J ∈ K), F_p[G] := F_p[t_1,…,t_{2k+1}]/(t_i^q − 1)."
*Lemma 2.2.* Unchanged (q odd).
*Lemma 2.3.* "In F_p[t]/(t^q − 1) put y := t − t^{−1}. (i) F_p[t]/(t^q−1) = F_p[y]/(y^q) and t ↦ t^{−1} becomes y ↦ −y; (ii) t_jt_k − 1 = (unit)(y_j + y_k); (iii) φ(u) = (u−1)^{q−1} in F_p[u]." Proof: "(i) t^q − 1 = (t−1)^q in characteristic p because q = p^v; t and t+1 = 2 + (t−1) are units because 2 ∈ F_p^×; y = t^{−1}(t−1)(t+1) …" — the rest verbatim with F_3 → F_p. "(ii) … t_j + t_k = 2 + (t_j−1) + (t_k−1) is a unit since 2 ∈ F_p^×." "(iii) (u−1)φ(u) = u^q − 1 = (u−1)^q by Frobenius, and F_p[u] is a domain."
*Definition of B, D.* Verbatim with F_p; "the second expression holds in Z[a,b] because q−2 is odd".
*Lemma 2.4.* "(i) (a+b)^{q−1}·b = −ab·D(a,b) in F_p[a,b]/(b^q)." Proof: "In characteristic p, (a+b)·Σ_{s=0}^{q−1}(−1)^s a^s b^{q−1−s} = (−1)^{q−1}a^q + b^q = a^q + b^q = (a+b)^q (telescoping; q−1 even; Frobenius), so (a+b)^{q−1} = Σ(−1)^s a^s b^{q−1−s} in the domain F_p[a,b]…" — the rest verbatim. "(ii)" verbatim.
*Prop 2.5.* Verbatim with F_p: "Let q = p^v, k ≥ 0, ∅ ≠ K ⊆ 𝒥. Then dim_{F_p} F_p[G]/(ψ̄_J) = q^{2k+1} − dim_{F_p}(D_J : J ∈ K)C, … H_{2k}(X)/L_K(X) is torsion free iff dim_{F_p}(D_J : J ∈ K)C = |Γ_K|." Proof verbatim.
*Prop 2.6.* Verbatim with F_p; "since ℓ^q = Σ c_i y_i^q for every linear form over F_p (c^q = c)".
*Theorem 5.3′ (any field, any odd q).* Statement as in §5 item (a) above; proof verbatim.
*Main Theorem′.* "Let p be an odd prime, q = p^v, k ≥ 0. Then H_{2k}(X;Z)/L(X) is torsion free for the Fermat variety of degree q and dimension 2k, and L(X) is primitive of rank Q_k(q)+1." Proof: Prop 2.5 (over F_p) turns the statement into dim_{F_p}(D_J)C = Q_k(q); ≤ is Prop 2.5, ≥ is Theorem 5.3′ at the root (Lemma 5.2 is field-free).
That is the whole change: three occurrences of "2 ∈ F_p^×" and three of "Frobenius, q = p^v". I would print the general statement and keep 3 only in the title and the examples. The previous referees' check "(S) over F_5 and F_7" is the sanity test; I would add (1,5) = 3·25 − 45 + 6 = 36 and (1,7) = 3·49 − 63 + 6 = 90 as printed numbers.

**Composite odd m.** Here the paper's method does not apply as it stands, and I think the reason is instructive. Write m = q·m' with q = p^v, p ∤ m'. Then F_p[t]/(t^m − 1) = F_p[t]/((t^{m'} − 1)^q) splits, by the Frobenius orbits of μ_{m'}, into local factors F_{p^d}[y]/(y^q); so F_p[G] is a product over the (Frobenius orbits of) characters χ of μ_{m'}^{2k+1}, and on the factor of χ the generator ψ̄_J becomes 0 if some χ(t_{j_i}t_{k_i}) ≠ 1, and otherwise (unit)·Π_{i : χ(t_{k_i}) = 1} y_{k_i} · Π_{i ≥ 1}(y_{j_i} + y_{k_i})^{q−1} after the same substitution y = s − s^{−1}, s := t/χ(t). So Conjecture 1.2 for composite m is equivalent to a family of statements (S)_χ, one per character: a dimension count in a box ring for the **subfamily** K_χ := {J : χ(t_{j_i}t_{k_i}) = 1 for all i} of matchings, with the y_{k_0}-type factors present only on the coordinates where χ is trivial. Two things follow. (1) A proof cannot go through any statement valid for all subfamilies (§7 shows such statements are false), so the special shape of K_χ must be used: K_χ is the set of matchings compatible with the involution-pairing of the coordinates induced by χ (coordinates i, j can be paired only if χ(t_i)χ(t_j) = 1). (2) The natural generalisation of Theorem 5.3 is a *coloured* version: partition the index set by the values χ(t_i) into classes {c, c^{−1}}; pairs must join a c-coordinate to a c^{−1}-coordinate; the point set becomes T^{m} with a different involution structure per colour; the residue and the partition λ(M) become multi-partitions, one per colour. The peeling of one variable and the chain of options should survive colour by colour; P2 and P3 would need to be redone in that setting. I would try it first at m = 15 = 3·5 with k = 1 (n = 2, where Degtyarev's theorem says the answer), then at (n,m) = (4,6), (4,10), (4,12), which [DS] confirmed by computer. My opinion: plausible, one new combinatorial theorem away, and the coloured P2 is where it will hurt.

**m = 2^v.** Here I expect a different proof, not a rewrite. Everything that made §2 work fails at once: 2 is not a unit (t+1 = t−1 is nilpotent), so there is no antisymmetric coordinate y with t_jt_k − 1 = (unit)(y_j + y_k); with y = t − 1 one gets y_j + y_k + y_jy_k, and the ideal is not generated by "linear" forms of a monomial-like shape. On the point side, −1 ∈ μ_m is its own inverse, so the count |Γ_𝒥| acquires the δ_m term of [DS, Remark 4.4] and the residue/class structure of §5 (fixed-point-free involution) is lost: Lemma 2.2 and Lemma 3.1 need a "self-paired value". Theorem A itself fails in characteristic 2 (Remark 6.3(1)), which suggests the algebra is genuinely different, not just harder. What I would do: compute the graded ranks of (ψ̄_J) in F_2[t]/(t_i^{2^v} − 1) at (k,m) = (1,4), (2,4), (1,8), (2,8) to see whether a monomial/leading-term structure analogous to Theorem 4.1 exists; if at q = 4 the leading monomials again form a ballot-like set, a direct Gröbner-type proof for m = 4 (all k) is the realistic first target. [DS] have confirmed (4,4), (4,8), (6,4) by computer, so the conjecture is not in doubt there; the method is.


---
*Referee: FABLE_3 (independent, no stake). Folder `~/Desktop/LECTORES_EN_FRIO/FABLE_3/`; code and logs in `checks/`; [DS] source in `checks/DS_source/`. No process left running. 24 September 2026.*
