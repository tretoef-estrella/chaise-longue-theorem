# INFORME_4 — misión «El lema de interacción» (2026-09-22)

## FIRST LINE
**(a)** (L1): NOT proved for all q (still proved for q ∈ {3, 9, 27}, all k ≥ 3; new reformulation and degree constraints, §1). (L2): NOT proved for k ≥ 3. Proved this turn, all q: the **slice lemma** (D(k) ⇒ J_1 ⊇ gr I(V_1) ⇒ c_k ≤ N_k; D'(k) ⇒ c'_k ≤ N'_k; D(k) ⇒ the +1 row r_{q−1} ≤ f_{+1}), hence **c_2 ≤ N_2 and c_3 ≤ N_3 for all q** from D(2), D(3) (items 1 and 4 of §4, the STEP 3 target, without G-a); gates (1,9), (2,9), (2,27) pass with equality J_1 = gr I(V_1).
**(b)** Missing, exact: (L1) «∃ γ_0, γ_1 ∈ F_3[a,a',b,b'] with ε_1(T−ε_4γ_0) ≡ (ε_1ε_2−ε_3)γ_1 mod box_q and ε_1γ_1 + ε_3γ_0 ≡ 0 mod box_{q−1}» for q ≥ 81 (cell: q = 81, 4 variables); (L2) «gr I(V'_1) ⊆ I^{(2k)} + (e_{2k}) + M'_k» and «gr I(V_1) ⊆ I^{(2k+1)} + M_k» for k ≥ 3 (cells (3,3), (3,9); G-a is the k = 2 even generic case at general q).
**(c)** **NO**: neither the conjecture nor the row k = 4 closes; the row needs (P_3), (P_4) for q ≥ 81 and (DO_3), (DO_4), (DE_4).

## STEP 0
STATE: CLOSED
BUDGET: 10 min (start 06:50). No runs.
**Facts of §1 I will use:** fact 1 (D(2), D(3) for all q; D(k) at q = 3) as inputs of the chain and of the pointwise criteria; fact 2 (c_k ≤ N_k ⟺ ℓ_{q−1} ≥ N_k when D(k), D'(k) hold) for STEP 3; fact 3 (degrees 2(q−3), 2(q−2); β-degree of γ_0 ≥ q−3; γ_0 ∉ F_3[r_1,r_2]) to shape the ansatz of STEP 1; fact 4 for (II).
**Check of fact 4 on paper.** B = F_3[a,a',b,b']/box_q. A monomial a^ia'^jb^kb'^l times r_1r_2 = aa'bb' lies in box_q iff i ≥ q−1 or j ≥ q−1 or k ≥ q−1 or l ≥ q−1; since box_q is monomial, f·r_1r_2 ∈ box_q iff every monomial of f does, so ann_B(ε_4) = (a^{q−1}, a'^{q−1}, b^{q−1}, b'^{q−1})B =: box_{q−1}·B. In (II), ε_3T ∈ box_q (each term of ε_3T = (β_1r_2 + β_2r_1)(r_1^{q−1} + r_2^{q−1}) contains a q-th power), so (II) ⟺ ε_4(ε_1γ_1 + ε_3γ_0) ∈ box_q ⟺ **ε_1γ_1 + ε_3γ_0 ∈ box_{q−1}**. ✓
**Also on paper (used below):** with γ_0 = ε_1δ, γ_1 = −ε_3δ, (II) holds exactly and (I) becomes ε_1T ≡ δ·(ε_1²ε_4 − ε_1ε_2ε_3 + ε_3²) = −δ·∏_{i<j}(x_i+x_j) (mod box_q) (INFORME_3 §1.4). At q = 3 this ansatz is impossible (δ would have degree −1), consistent with γ_0 = −1 there; so the Koszul-type syzygies of (ε_3, ε_1) are not enough and the box_{q−1} syzygies matter.
NEXT: STEP 1.

## STEP 1
STATE: NOT CONCLUDED
BUDGET: 45 min (start 06:52; write from 07:28). Runs: `l1a.m2` (q = 3, 9; 0.6 s, 153 MB), `l1b.m2` (q = 9 only; 2 s, 195 MB). No q = 27 run this step.

### 1.1 Reformulations (PROVED, pencil)
- With U := T − ε_4γ_0 the system is (I) ε_1U ≡ (ε_1ε_2−ε_3)γ_1, (II) ε_3U ≡ ε_1ε_4γ_1 (mod box_q); by fact 4, (II) ⟺ ε_1γ_1 + ε_3γ_0 ∈ box_{q−1}.
- Generating-function form: with E(u) := ∏_{i}(1+x_iu) over the four variables, E_+ = 1+ε_2u²+ε_4u⁴, E_− = ε_1u+ε_3u³, the infinite γ-recurrence of INFORME_3 §1.1 is equivalent to: **the series Ω(u) := [γ_1(1+ε_1u) + Uu²]/E(u) is EVEN in u (mod box_q)**. Since E(u)^q ≡ 1 mod box_q (Frobenius), 1/E(u) ≡ E(u)^{q−1} = ∏_i Σ_{j<q}(−x_iu)^j (Lucas), so equivalently **[γ_1(1+ε_1u) + Uu²]·E(u)^{q−1} is an even polynomial in u mod box_q**, with U ≡ T mod ε_4. Expanding gives back exactly (I),(II) (coefficients of u³, u⁵), so this is a restatement, but it exhibits the mechanism: (I),(II) say that γ_1(1+ε_1u)+Uu² is «E(u) times an even series», and the u¹-coefficient condition is automatic.
- The k = 2 certificate (which exists by D'(2) + PLUS lemma) satisfies only the top two conditions [γ_2 + ε_2γ_1 + ε_4γ_0 ≡ T, ε_1γ_2 + ε_3γ_1 ≡ 0]; (P_3) needs one more, (ε_1ε_2−ε_3)γ_2 + ε_1ε_4γ_1 ≡ 0, and (P_k) needs the whole tail. So D'(2) does not give (P_3): the known level does not lift. Also D(3) (fact 1) gives new elements of I^{(7)} (x_{C'}x_B^{q−1} with |C'| = 8−2j, |B| = j, from the «−» detectors of Z_8 restricted to x_7 = 0) but not (P_3): a vanishing polynomial on Z_8 producing x_C(x_A^{q−1}+x_B^{q−1}) after x_7 ↦ 0 would need a correction of top degree ≥ 3(q−1) (it must detect x_7 ≠ 0 and a parity), which kills the projection.
- Duality (Gorenstein B, socle functional φ): (I),(II) solvable ⟺ φ(ε_1T·w_1) = 0 for all w_1 ∈ π_1(Ker Matᵀ); π_1(Ker Matᵀ) ⊆ ann_B(∏_{i<j}(x_i+x_j)), and equality would force ε_1T ∈ (∏(x_i+x_j)) which is false at q = 3 by degree. So the obstruction sits in the finer structure of Ker Matᵀ; not resolved.

### 1.2 Ansatz results (MEASURED, gates)
- γ_0 = ε_1^{q−3}·ρ(r_1,r_2) with γ_1 free: works at q = 3 (ρ = −1), FAILS at q = 9 (`l1a.log`).
- Pair-symmetric ring F_3[β_1,β_2,r_1,r_2], swap-symmetric solutions, β-degree caps: at q = 9 the minimal caps are **β-deg(γ_0) ≤ 6 = q−3 and β-deg(γ_1) ≤ 8 = q−1** (caps 0, 2, 4, 6 on γ_1 fail; `l1b.log`), matching q = 3 (γ_0 = −1: β-degree 0 = q−3; γ_1 = r_1+r_2−ε_1²: β-degree 2 = q−1) and fact 3. The solution printed has 51 + 77 terms and is one point of an affine space; no q-symbolic form was read off.
- Consequence (PROVED): if a q-uniform formula exists in the symmetric ring, it has β-degrees exactly (q−3, q−1) and r-degrees ((q−3)/2, (q−3)/2) at the top β-terms.

**Missing lemma (exact, unchanged):** «for every q = 3^v there exist γ_0, γ_1 ∈ F_3[a,a',b,b'] with ε_1(T−ε_4γ_0) ≡ (ε_1ε_2−ε_3)γ_1 mod box_q and ε_1γ_1 + ε_3γ_0 ≡ 0 mod box_{q−1}, T = (aa')^{q−1}+(bb')^{q−1}»; equivalently «[γ_1(1+ε_1u)+(T−ε_4γ_0)u²]·∏_i(1+x_iu)^{q−1} is even in u mod box_q». Cells: q = 3, 9, 27 true; q = 81 in 4 variables (allowed, not run: the q = 27 module computation took 20 s / 500 MB and q = 81 would exceed 10 min by the degree-(2q) growth).
NEXT: STEP 2.

## STEP 2
BUDGET: 90 min (start 07:05; write from 08:17). Runs: point-data on Z_5(F_9) (seconds, < 300 MB); memberships in the gate cells with estimates before each.


**Rule-10 incident (declared):** `z5.m2` (enumeration of Z_5(F_9) point by point and dense ranks over GF(9)) exceeded 10 minutes and was killed by me before printing anything; nothing from it is used. Estimate error: 9^5 loop iterations with `tally` plus rank computations of ~10^3 × 10^3 matrices over GF(9) in M2.

### 2.1 SLICE LEMMA (PROVED, pencil): what a known level gives for free
Let X ⊂ F_q^{n} be a finite set closed under scaling (x ↦ λx, λ ∈ F_q^×), X_1 := {y ∈ F_q^{n−1} : (y,1) ∈ X} its slice, π: x_{n−1} ↦ 0. For f ∈ I(X_1) of degree d let G(y, x_{n−1}) := x_{n−1}^d f(y/x_{n−1}) be its homogenization (homogeneous of degree d, G(y,0) = top(f)). Then x_{n−1}·G vanishes on X: at a point (y,t) ∈ X with t ≠ 0, (y/t, 1) ∈ X so y/t ∈ X_1 and G(y,t) = t^d f(y/t) = 0; at t = 0 the factor x_{n−1} vanishes. As x_{n−1}G is homogeneous it is its own top form, so x_{n−1}G ∈ gr I(X), G ∈ gr I(X) : x_{n−1}, and top(f) = π(G) ∈ π(gr I(X) : x_{n−1}). Hence
> **gr I(X_1) ⊆ π(gr I(X) : x_{n−1}).**
Apply to X = Z_{2k+2} (closed under scaling), X_1 = V_1 (|V_1| = N_k): **if D(k) holds** then gr I(Z_{2k+2}) = I^{(2k+2)} (floor + equal dimensions), so **J_1 ⊇ gr I(V_1) and c_k = dim S/J_1 ≤ dim S/gr I(V_1) = N_k.** Likewise **D'(k) ⇒ J'_1 ⊇ gr I(V'_1) ⇒ c'_k ≤ N'_k.** ∎
Consequences: with fact 1, **c_2 ≤ N_2 and c_3 ≤ N_3 for all q = 3^v** (items 1 and 4 of §4 of the mission), without G-a and without the Jordan-layer statement of fact 2 (which it implies: ℓ_{q−1} ≥ N_k). This is the STEP 3 target, obtained here.
**Rows.** For the +1 fibre: f ∈ I(F_{+1}) ⇒ f(y')·(1 − (x_{2k} − 1)^{q−1}) vanishes on V_1 (it is f·[x_{2k} = 1]) and its top form is x_{2k}^{q−1}·top(f); so top(f) ∈ gr I(V_1) : x_{2k}^{q−1} and, given D(k), **R_{q−1} ⊇ π'(gr I(V_1) : x_{2k}^{q−1}) ⊇ gr I(F_{+1}), i.e. r_{q−1} ≤ f_{+1}** for that k (and R'_{q−1} ⊇ gr I(F'_{+1}) given D'(k)). For a generic value v the same trick gives only top(f) ∈ R_{q−1} (the indicator [x_{2k} = v] has degree q−1), not the generic row: the generic row is a genuine degree phenomenon (G-a).
Limits: the lemma uses D(k) as input; it does not feed the chain at level k (there D(k) is the output). It does not give the rows of the EXPLICIT ideal K_k (⊆ J_1), so (DE_k) is untouched.
Numerical gate of the slice lemma (`slice.log`): gr I(V_1) ⊆ J_1 and in fact **J_1 = gr I(V_1)** in (1,9) (24 = 24) and (2,9) (855 = 855), computing gr I(V_1) as gr(G_{2k+1}({1})) with G radical (mission 2 §2.2).

### 2.2 The two dimension statements as inclusions of top-form ideals (PROVED reformulation)
Given D(k−1) and (P_k): K'_k ⊆ J'_1 ⊆ gr I(V'_1) — the second inclusion because I^{(2k+1)} ⊆ gr I(Z_{2k+1}) (floor) and the slice lemma's layer structure: π(gr I(Z_{2k+1}) : x_{2k}^a) ⊇ gr I(V'_1) for a ≥ 1, with Σ_a (colengths of the layers of gr I(Z_{2k+1})) = P'_k = P_{k−1} + (q−1)N'_k and layer 0 = gr I(Z_{2k}) = I^{(2k)} of colength P_{k−1}, forcing every layer a ≥ 1 to be exactly gr I(V'_1); then I^{(2k+1)} ⊆ gr I(Z_{2k+1}) gives J'_1 ⊆ gr I(V'_1). Hence dim S/K'_k ≥ dim S/J'_1 ≥ N'_k and
> **(DO_k) ⟺ gr I(V'_1) ⊆ K'_k = I^{(2k)} + (e_{2k}) + M'_k**, and likewise (given D'(k)) **(DE_k) ⟺ gr I(V_1) ⊆ K_k = I^{(2k+1)} + M_k.**
So the interaction lemma (L2) is exactly: every top form of a polynomial vanishing on the slice lies in the explicit ideal. The slice lemma proves the analogous statement for the COLON ideals from a KNOWN level (gr I(V_1) ⊆ J_1 from D(k)); the chain needs it for the explicit ideals with the level unknown.
Also: the chain hypothesis «c_{k−1} ≤ N_{k−1}» is automatic from D(k−1) (slice lemma), so row 1 of K'_k is exact without extra input.

### 2.3 Attempts at (L2) and where they stop (declared)
- The «+1 row» part of (L2): given D(k) the slice lemma gives R_{q−1} ⊇ gr I(F_{+1}) for the COLON ideal J_1 (§2.1). For the explicit K_k I proved (INFORME_3 §2.3) the +1 row for k = 2 by the monomials of M_2; for general k the analogous elements x_Cx_{A'}^{q−1} ∈ R^K_{q−1} come from M_k (|A'| = j−1, |C| = 2k+1−2j), which match the measured generators of Q = ∩_{i<j}[(y_i,y_j)+I^{(2k−2)}] in (2,9), (2,27), (3,3) (INFORME_2 §2.4); the inclusion gr I(F_{+1}) ⊆ Q is proved (INFORME_2 §1.2) and Q ⊆ R^K_{q−1} is the generation statement, not proved for k ≥ 4.
- The generic rows: no mechanism found beyond G-a's numerical truth; a vanishing polynomial with the right top form must produce x_{2k}^a·m with 2 ≤ a ≤ q−2, and every indicator-type construction ([x_{2k} = v] has degree q−1) lands in the top layer instead. The tablero's generic rows are a degree phenomenon that no point-set construction of mine reaches.
- I did not find a mechanism for D'(k) from D(k): the natural candidate («x_6·G_f ∈ gr I(V_1) for f ∈ I(F_0)») is false as stated (x_6G_f does not vanish on V_1).

STATE: NOT CONCLUDED for (L2) in general.
Summary STEP 2: PROVED: the slice lemma (gr I(X_1) ⊆ π(gr I(X) : x_{n−1}) for X closed under scaling) with consequences D(k) ⇒ c_k ≤ N_k, D'(k) ⇒ c'_k ≤ N'_k, D(k) ⇒ R_{q−1} ⊇ gr I(F_{+1}); the reformulations (DE_k) ⟺ gr I(V_1) ⊆ K_k, (DO_k) ⟺ gr I(V'_1) ⊆ K'_k. Not proved: (L2) for any k ≥ 3 (and G-a for general q). Gates: `slice.log` (1,9), (2,9).
NEXT: STEP 3.

## STEP 3
BUDGET: 30 min (start 07:20; write from 07:44). Run: `slice27.m2` = gate (2,27) of the slice lemma (6 variables, q = 27; estimate ~2 min, < 800 MB).

### 3.1 c_2 ≤ N_2 and c_3 ≤ N_3 for all q = 3^v: PROVED
By the slice lemma (§2.1) with X = Z_{2k+2}: D(k) ⇒ J_1 ⊇ gr I(V_1) ⇒ c_k ≤ N_k. Fact 1 gives D(2) and D(3) for all q, hence **c_2 ≤ N_2 and c_3 ≤ N_3 for all q**. With D'(2) (mission 2) the ladder then forces c_2 = N_2 and J_1 = gr I(V_1) at level 2; at level 3, c_3 ≤ N_3 holds unconditionally (D'(3) is not needed for it; it is needed only to turn it into D(3), which is already known).
In the language of fact 2: ℓ_{q−1}(k) = dim x_{2k+1}^{q−1}A_k ≥ N_k follows, since the non-increasing layers ℓ_1 ≥ … ≥ ℓ_{q−1} sum to (q−1)N_k (given D(k), D'(k)) and ℓ_1 = c_k ≤ N_k forces all of them to equal N_k. The character-projection gap at a = q−1 described in fact 2 is bypassed: the homogenization argument never projects, it multiplies by x_{2k+1}.
Gates: (2,9): J_1 = gr I(V_1), 855 = 855 (`slice.log`); **(2,27): J_1 = gr I(V_1), 9765 = 9765 (`slice27.log`, 39 s, 265 MB)**. Level 3 at q = 3: covered by fact 1 (Steinberg) and by the lemma; (3,9) not run (not needed: the statement is proved for all q).

### 3.2 What this changes in the chain and in the fallback
- The chain hypothesis c_{k−1} ≤ N_{k−1} is automatic from D(k−1): the chain at level k needs only (P_k), (DO_k) [⇒ D'(k)] and (DE_k) [⇒ D(k)].
- Fallback §4: items 1 and 4 are PROVED for all q. Items 2 ((P_3), (P_4)) are proved for q ≤ 27 (INFORME_3) and open for q ≥ 81 (STEP 1). Items 3, 5, 6 ((DO_3), (DO_4), (DE_4)) are open: by §2.2 they are the inclusions gr I(V'_1) ⊆ K'_3, gr I(V'_1) ⊆ K'_4, gr I(V_1) ⊆ K_4.
STATE: CLOSED (target of the step reached for both levels, for all q).
NEXT: STEP 4.

## STEP 4 — VERDICT
STATE: CLOSED. (Start 07:16; budget 15 min.)

**Proved this turn (proofs in this report):**
1. **Slice lemma** (§2.1): for X ⊂ F_q^n closed under scaling, gr I(X_1) ⊆ π(gr I(X) : x_{n−1}); hence D(k) ⇒ J_1 ⊇ gr I(V_1) ⇒ c_k ≤ N_k, and D'(k) ⇒ c'_k ≤ N'_k; also D(k) ⇒ R_{q−1} ⊇ gr I(F_{+1}). Gates: (1,9), (2,9), (2,27) with equality J_1 = gr I(V_1) (`slice.log`, `slice27.log`).
2. **c_2 ≤ N_2 and c_3 ≤ N_3 for all q** (§3.1), from D(2), D(3) (fact 1); the level-2 and level-3 gate of §3 of the mission, without G-a.
3. Reformulation (§2.2): (DO_k) ⟺ gr I(V'_1) ⊆ K'_k and (DE_k) ⟺ gr I(V_1) ⊆ K_k (given D(k−1)+(P_k), resp. D'(k)); the chain hypothesis c_{k−1} ≤ N_{k−1} is automatic.
4. (L1): the evenness reformulation «[γ_1(1+ε_1u)+(T−ε_4γ_0)u²]·∏(1+x_iu)^{q−1} even mod box_q»; the β-degree pattern (q−3, q−1) confirmed at q = 3, 9; the ansatz γ_0 = ε_1^{q−3}ρ(r_1,r_2) fails at q = 9; the k = 2 certificate does not lift; D(3) gives new elements of I^{(7)} but not (P_3).

**Not proved:** (L1) for q ≥ 81; (L2) for any k ≥ 3 (and G-a for general q); (DO_3), (DO_4), (DE_4).

**Chain / fallback:** items 1 and 4 of §4 closed for all q; items 2 (q ≤ 27 only), 3, 5, 6 open. **CONJECTURE 1.2: NOT CLOSED. Row k = 4: NOT CLOSED.**

**Numbers, cells, logs:** `l1a.log` (q = 3, 9), `l1b.log` (q = 9; caps 6/8; 51+77 terms), `slice.log` (24 = 24, 855 = 855), `slice27.log` (9765 = 9765; 39 s, 265 MB). All completed runs < 40 s and < 300 MB.

**Rule-10 incidents (declared):** `z5.m2` exceeded 10 min (point enumeration of Z_5(F_9) and dense ranks over GF(9)) and was killed with no output used (§2 head). No other incident.

**On MISION_4.md:** no errors found. Two precisions: (i) fact 2 is superseded for the chain's purpose by the slice lemma, which needs only D(k) (not D'(k)) and needs no projection; (ii) the fallback item 4 (c_3 ≤ N_3) needs only D(3), not D'(3).
