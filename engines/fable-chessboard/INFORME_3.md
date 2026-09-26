# INFORME_3 — misión «Las casillas sin colon» (2026-09-21)

## FIRST LINE
**(a)** k = 2 NOT closed: G-a remains open for general q (proved only at q = 9, 27). Level 3 NOT closed (it needs c_2 ≤ N_2, i.e. (DE_2), i.e. G-a). Proved this turn: **(DO_2) for all q** (§3.1); **(DE_2) ⟺ G-a**, with the +1 even row of K_2 proved for all q (§2.3); **(P_k) reduced with k as a letter to a k-independent two-unknown system (I),(II) in F_3[a,a',b,b']** (§1.1), and **(P_k) proved for all k ≥ 3 at q ∈ {3, 9, 27}** with gates (3,3), (4,3), (3,9) passed; the exact layer structure of the explicit casillas K_k, K'_k (rows 0, 1 exact; (DE_k), (DO_k) ⟺ their outer rows; the sum of colons cannot suffice) (§2.1, §3.2); the pointwise criterion for rows (§2.2); the three STEP 0 debts.
**(b)** Missing lemmas, exact: (1) «for every q = 3^v there are γ_0, γ_1 ∈ F_3[a,a',b,b'] with ε_1(T − ε_4γ_0) ≡ (ε_1ε_2−ε_3)γ_1 and ε_3(T − ε_4γ_0) ≡ ε_1ε_4γ_1 mod (a^q,a'^q,b^q,b'^q), T = (aa')^{q−1}+(bb')^{q−1}» (cell: q = 81, 4 variables) ⇒ (P_k) all k, q; (2) G-a: «x_4²x_0²x_1^{q−2} ∈ I^{(5)} + M_2 + (x_4³) for all q» (cells q = 9, 27 true) ⇒ (DE_2); (3) the interaction elements of the outer rows of K_k, K'_k for k ≥ 3 (cells (3,3), (3,9)).
**(c)** **NO.** The chain stops at the even step of level 2: everything from D(2) (via the chain) upward needs G-a, and (P_k) for q ≥ 81 needs lemma (1).

## STEP 0
STATE: CLOSED
BUDGET: 15 min (start 22:12). Run estimate: < 1 min, < 400 MB.
**Calibration.** `casilla.m2` as is: 8/8 `equal:true`, `FIN-OK` (`casilla.log`, 0.78 s, 205 MB): EVEN (1,9) 24, (2,3) 45, (2,9) 855, (3,3) 357; ODD (1,9) 2, (2,3) 16, (2,9) 88, (3,3) 126.

**Debt 1 — odd Lemma E, written out.** Let N = 2k+1, I' := I^{(2k+1)} ⊂ S_{2k+1}, y := (x_0..x_{2k−2}), ε_j := e_j(y), ℓ := e_1(x_0..x_{2k−1}) = ε_1 + x_{2k−1}. Substitute x_{2k} = −ℓ (kills e_1) and x_{2k−1} = ℓ − ε_1, so S_{2k+1}/(e_1) ≅ S_{2k} = S_{2k−1}[ℓ]. Then e_j(x_0..x_{2k}) = ε_j + (x_{2k−1}+x_{2k})ε_{j−1} + x_{2k−1}x_{2k}ε_{j−2} = ε_j − ε_1ε_{j−1} + ℓ(ε_1−ℓ)ε_{j−2}, i.e. **E_j ≡ P'_j + ℓ·ε_1ε_{j−2} (mod ℓ²)**, P'_j := ε_j − ε_1ε_{j−1}; and x_{2k−1}^q = (ℓ−ε_1)^q ≡ −ε_1^q ∈ (y^q), x_{2k}^q ≡ 0 (mod ℓ²). Let K := φ(I') = (E_3, …, E_{2k+1}, y^q) with φ: x_{2k} ↦ −ℓ (kernel (e_1) ⊆ I'). (a) φ(I' : x_{2k}) = K : ℓ [if f'·x_{2k} ∈ I' then φ(f')·(−ℓ) ∈ K; conversely fℓ ∈ K, lift f to f' with φ(f') = f, then φ(f'x_{2k}) ∈ φ(I') ⇒ f'x_{2k} ∈ I' + ker φ = I']. (b) For any ideal A ∋ e_1 of S_{2k+1}: every f = f̃ + e_1h with f̃ = φ(f) ∈ S_{2k}, so A = (A ∩ S_{2k}) + (e_1) and π(A) = φ(A) + π(e_1) = φ(A) + (ℓ). Hence **J'_1 = π(I' : x_{2k}) = (K : ℓ) + (ℓ)**. (c) Let ψ: S_{2k} → S_{2k−1}, x_{2k−1} ↦ −ε_1 (kernel (ℓ)); J̄'_1 := ψ(J'_1) = {f̃ ∈ S_{2k−1} : ℓf̃ ∈ K + (ℓ²)} = the ℓ-coefficients of the elements of K + (ℓ²) with zero ℓ-free part. Writing an element of K as Σ_j(g_j + ℓg_j')E_j + Σ_i(h_i + ℓh_i')y_i^q, its free part is Σ_jg_jP'_j + Σh_iy_i^q and its ℓ-part is ε_1Σ_jg_jε_{j−2} + Σg_j'P'_j + Σh_i'y_i^q. Therefore **J̄'_1 = K'_0 + ε_1·N'**, K'_0 := (P'_3, …, P'_{2k+1}, y^q), **N' := { Σ_{j odd, 3≤j≤2k+1} g_j·ε_{j−2} : Σ_j g_jP'_j ∈ (y^q) }** (an ideal of S_{2k−1}). Since y has only 2k−1 variables, P'_{2k+1} = ε_{2k+1} − ε_1ε_{2k} = 0, so g_{2k+1} is unconstrained and **ε_{2k−1} = y_0⋯y_{2k−2} ∈ N'**. (d) Rows: J'_1 : x_{2k−1}^a ∋ ℓ, so by (b) applied to S_{2k} → S_{2k−1}: π'(J'_1 : x_{2k−1}^a) = ψ(J'_1 : x_{2k−1}^a) + (ε_1) = (ψ(J'_1) : ψ(x_{2k−1})^a) + (ε_1) [ψ is surjective with kernel inside the ideal, so it commutes with the colon], i.e. **R'_a = (J̄'_1 : ε_1^a) + (ε_1)**. ∎ (Numerically: reproduces all odd rows of (1,9), (2,3), (2,9), (3,3): `paso2b.log`.)

**Debt 2 — N' and ε_1(y_i+y_j)^{q−1} ∈ N' for k = 2.** With N' as in (c) and k = 2 (y = (y_0,y_1,y_2)): N' = {g_3ε_1 + g_5ε_3 : g_3P'_3 + g_5·0 ∈ (y^q)} = ε_1·((y^q) : P'_3) + (ε_3). The identity (y_0+y_1)(y_0+y_2)(y_1+y_2) = ε_1ε_2 − ε_3 gives P'_3 = −(y_0+y_1)(y_0+y_2)(y_1+y_2). For g_3 := (y_i+y_j)^{q−1}: g_3P'_3 = −(y_i+y_j)^q·(the other two factors) = −(y_i^q + y_j^q)(…) ∈ (y^q). Hence (y_i+y_j)^{q−1} ∈ (y^q) : P'_3 and **ε_1(y_i+y_j)^{q−1} ∈ N'**, so ε_1²(y_i+y_j)^{q−1} ∈ J̄'_1. ∎

**Debt 3 — the +1 even row of k = 2, r_{q−1} ≤ 2(3q−4), all q.** R_{q−1} = {m ∈ S_4 : x_4^{q−1}m ∈ J_1} ⊇ (e_1, e_3, x_i^q) (J_0 ⊆ J_1, Lemma C). U-a (mission 1 §2.4): x_ix_jx_l ∈ R_{q−1} for i<j<l ≤ 3. U-b (now proved, §2.3 of MISION_3: M_2 ⊆ J_1 given D'(2), with A = {a,4}, B = {b,b'}, C = {c}): x_cx_a^{q−1}x_4^{q−1} ∈ J_1 ⇒ x_cx_a^{q−1} ∈ R_{q−1}. In reduced coordinates x_0 = −(x_1+x_2+x_3), revlex x_1 > x_2 > x_3, R̄_{q−1} contains x_1x_2x_3, x_ix_j(x_i+x_j) [from x_0x_ix_j], x_i^q, x_ix_j^{q−1} (i<j ≤ 3), with leading monomials x_1x_2x_3, x_1²x_2, x_1²x_3, x_2²x_3, x_1^q, x_2^q, x_3^q, x_1x_2^{q−1}, x_1x_3^{q−1}, x_2x_3^{q−1}. Standard monomials x_1^αx_2^βx_3^γ of that monomial ideal: α ≥ 2 ⇒ β = γ = 0, 2 ≤ α ≤ q−1: q−2; α = 1 ⇒ βγ = 0: x_1x_3^γ (γ ≤ q−2) and x_1x_2^β (1 ≤ β ≤ q−2): 2q−3; α = 0 ⇒ β ≤ 1 or γ = 0: x_3^γ (γ ≤ q−1), x_2x_3^γ (γ ≤ q−2), x_2^β (2 ≤ β ≤ q−1): 3q−3. Total **6q−8 = 2(3q−4) = f_{+1}(2,q)** (q = 3 gives 10 = r_2(2,3)). Hence r_{q−1}(2,q) ≤ f_{+1}(2,q) for all q. ∎ (Together with mission 1: the even generic row of k = 2 still needs G-a.)
NEXT: STEP 1.

## STEP 1
BUDGET: 40 min (start 22:20; write from 22:52). Runs: memberships in F_3[a,a',b,b'] at q = 9, 27 (4 variables, no colon; < 1 min, < 300 MB each).

### 1.1 Reduction of (P_k), with k as a letter, to a k-INDEPENDENT system in four variables (PROVED)
Variables: C (|C| = 2k−3, odd), a, a', b, b'. Write σ_n := e_n(x_C) (so σ_n = 0 for n > 2k−3) and ε_p := e_p(a,a',b,b'), p = 0..4; r_1 := aa', r_2 := bb', β_1 := a+a', β_2 := b+b', so ε_1 = β_1+β_2, ε_2 = r_1+r_2+β_1β_2, ε_3 = β_1r_2+β_2r_1, ε_4 = r_1r_2. Then e_m(all) = Σ_{p=0}^{4} ε_p·σ_{m−p}, and the target of (P_k) is x_C(x_a^{q−1}x_{a'}^{q−1} + x_b^{q−1}x_{b'}^{q−1}) = σ_{2k−3}·T with **T := r_1^{q−1} + r_2^{q−1}**.
A certificate σ_{2k−3}T ≡ Σ_{m odd ≤ 2k+1} c_m e_m (mod box) with c_m ∈ F_3[a,a',b,b'] exists iff, comparing the coefficients of the algebraically independent σ_n (n ≤ 2k−3; the σ_n with n > 2k−3 vanish), for every 0 ≤ n ≤ 2k−3: Σ_{p: n+p odd} c_{n+p}ε_p ≡ T·δ_{n,2k−3} mod (a^q,a'^q,b^q,b'^q). (The box of C-variables and of the four variables together is the box of I^{(2k+1)}.) Put γ_i := c_{2k+1−2i}. The conditions read:
 γ_2 + ε_2γ_1 + ε_4γ_0 ≡ T;  ε_1γ_2 + ε_3γ_1 ≡ 0;  and for 3 ≤ i ≤ k: γ_i + ε_2γ_{i−1} + ε_4γ_{i−2} ≡ 0, ε_1γ_i + ε_3γ_{i−1} ≡ 0.
**They do not depend on k except through the length of the chain.** Let Γ(t) := Σ_{i≥0}γ_it^i. An INFINITE sequence satisfies all of them iff (1+ε_2t+ε_4t²)Γ ≡ γ_0 + (γ_1+ε_2γ_0)t + Tt² and (ε_1+ε_3t)Γ ≡ ε_1γ_0 + (ε_1γ_1+ε_3γ_0)t (mod box, coefficientwise). Given γ_0, γ_1, define Γ := [γ_0 + (γ_1+ε_2γ_0)t + Tt²]/(1+ε_2t+ε_4t²) (invertible: constant term 1); the second identity then holds iff (ε_1+ε_3t)(γ_0+(γ_1+ε_2γ_0)t+Tt²) ≡ (ε_1γ_0+(ε_1γ_1+ε_3γ_0)t)(1+ε_2t+ε_4t²), i.e. iff
> **(I)** ε_1T ≡ ε_1ε_4γ_0 + (ε_1ε_2 − ε_3)γ_1  and  **(II)** ε_3T ≡ ε_4(ε_1γ_1 + ε_3γ_0)  (mod (a^q,a'^q,b^q,b'^q)).
Truncating the infinite solution at i = k gives a certificate for that k (the finite system has no conditions beyond i = k). Hence:
> **(P_k) for ALL k ≥ 3 ⟸ ∃ γ_0, γ_1 ∈ F_3[a,a',b,b'] satisfying (I) and (II).**
Remarks: ε_3T ∈ box and ε_4T ∈ box (each term contains a q-th power), and ε_1T ≡ β_2r_1^{q−1} + β_1r_2^{q−1}. The naive Koszul choice (γ_0 = γ_1 = 0 except the top) fails: it would need T ∈ ε_4·F_3[…] (`pk.log`: T ∉ e_2·D + (r_1r_2) + box with the restricted ansatz).

### 1.2 The system (I),(II) is solvable at q = 3, 9, 27; gates passed (PROVED for those q, all k ≥ 3)
`pk2.log`: at q = 9 and q = 27, M2 finds γ_0, γ_1 ∈ F_3[a,a',b,b'] with (I) and (II) (checked: «check I: true II: true»). Building c_m from the recurrence Γ = [γ_0 + (γ_1+ε_2γ_0)t + Tt²]/(1+ε_2t+ε_4t²) and verifying σ_{2k−3}T ≡ Σ c_me_m mod box in 2k+1 variables: **gate (3,9) passed** (`pk2.log`). Hence, by §1.1, **(P_k) holds for every k ≥ 3 at q = 9 and at q = 27** (a finite polynomial-identity verification at that q, valid for all k because the system is k-independent). Neither γ_0 = 0 nor γ_1 = 0 is possible (`pk2.log`).
`pk3.log`: solutions also at q = 3, and **gates (3,3), (4,3), (3,9) all pass** («certificate exact mod box? true»). Hence **(P_k) is PROVED for all k ≥ 3 at q ∈ {3, 9, 27}**. At q = 3 the normal-form solution is closed: γ_0 = −1, γ_1 = −(a−a')² − (b−b')² + β_1β_2 = r_1 + r_2 − ε_1² (using (a−a')² = β_1² − r_1 and β_1² − β_1β_2 + β_2² = ε_1² in char 3). At q = 9, 27 the normal forms are dense (115/215 and 1393/2996 terms): the normal form depends on the term order and is not a good guide.

### 1.3 Symmetric solutions and the q-general question
`pk4.log`: with γ_0, γ_1 restricted to F_3[β_1,β_2,r_1,r_2] (pair-symmetric ansatz), the system (I),(II) is solvable at q = 3 (γ_0 = −1, γ_1 = −β_1²+β_1β_2−β_2²+r_1+r_2) and at q = 9 (γ_0 has leading pieces r_1^6, r_2^6 = r_i^{q−3}; γ_1 has r_1^7, r_2^7 = r_i^{q−2}; full expressions in the log). The solutions are not unique (coset of the homogeneous solutions), so the printed representatives are not canonical, and I did not find the q-symbolic form in the time.
**Rule-10 incident (declared):** the run `pk4.m2` (symmetric ansatz at q = 3, 9, 27) exceeded 10 minutes at q = 27 (linear algebra on the monomial basis of degree 2q+1 in 4 variables, which I under-estimated) and was killed by me; only its q = 3, 9 output is used.

### 1.4 Structural facts about (I),(II) (PROVED, pencil)
- det(Mat) = ε_1²ε_4² − (ε_1ε_2−ε_3)ε_3ε_4 = ε_4·(ε_1²ε_4 − ε_1ε_2ε_3 + ε_3²) = −ε_4·∏_{i<j}(x_i+x_j) (Vieta identity for four variables: ∏_{i<j}(x_i+x_j) = e_1e_2e_3 − e_3² − e_1²e_4). Hence the cokernel of Mat over B := F_3[a,a',b,b']/box is annihilated by ε_4∏_{i<j}(x_i+x_j).
- ε_3T ∈ box, ε_4T ∈ box, ε_1T ≡ β_2r_1^{q−1} + β_1r_2^{q−1}. And r_1^{q−1} ∈ ((a+a')^{q−1}) + (a^q,a'^q) (Gorenstein: the socle (aa')^{q−1} of F_3[a,a']/(a^q,a'^q) lies in every nonzero ideal), so T·∏_{i<j}(x_i+x_j) ∈ box: the necessary condition from the determinant holds with γ_0 = 0, yet γ_0 = 0 is NOT sufficient (`pk2.log`). So the obstruction is finer than the determinant.

STATE: NOT CONCLUDED.
Summary STEP 1: PROVED with k as a letter: (P_k) for all k ≥ 3 ⟸ solvability of the k-independent system (I),(II) in F_3[a,a',b,b']/(a^q,a'^q,b^q,b'^q) (§1.1); PROVED: (P_k) for all k ≥ 3 at q ∈ {3, 9, 27} (solutions found, gates (3,3), (4,3), (3,9) passed: `pk2.log`, `pk3.log`). **Missing lemma (exact):** «for every q = 3^v there exist γ_0, γ_1 ∈ F_3[a,a',b,b'] with ε_1(T − ε_4γ_0) ≡ (ε_1ε_2−ε_3)γ_1 and ε_3(T − ε_4γ_0) ≡ ε_1ε_4γ_1 mod (a^q,a'^q,b^q,b'^q), T = (aa')^{q−1} + (bb')^{q−1}»; cell: q = 81 in 4 variables (allowed as a membership in ≤ 5 variables, no colon; not run).
NEXT: STEP 2.

## STEP 2
BUDGET: 70 min (start 22:38; write from 23:34). Runs: memberships and dimension counts in the gate cells (2,9), (2,27), (3,3), (3,9), (4,3); each estimated < 2 min, < 500 MB, estimate written before each run.

### 2.1 The layers of the explicit ideal K_k = I^{(2k+1)} + M_k along x_{2k} (PROVED, given D'(k), D(k−1), (P_k), (DO_k))
Write I := I^{(2k+1)}, rows R^K_a := π'(K_k : x_{2k}^a) ⊂ S_{2k}, R^I_a := π'(I : x_{2k}^a). Then dim S_{2k+1}/K_k = Σ_a dim S_{2k}/R^K_a (mission 2, §2.3) and R^K_a ⊇ R^I_a + π'(M_k : x_{2k}^a).
- **Rows of I along x_{2k}.** R^I_0 = I^{(2k)} (dimension A_{k−1} = P_{k−1}); R^I_1 = J'_1; the R^I_a increase with a. Given D'(k): P'_k = A'_k = Σ_a dim S_{2k}/R^I_a ≤ P_{k−1} + (q−1)·dim S_{2k}/J'_1 = P_{k−1} + (q−1)c'_k, and c'_k ≤ N'_k (chain), while P'_k = P_{k−1} + (q−1)N'_k. Hence c'_k = N'_k, all layers a ≥ 1 have dimension N'_k, and since they form an increasing chain of ideals of equal colength, **R^I_a = J'_1 for all 1 ≤ a ≤ q−1**. Moreover J'_1 ⊇ K'_k with dim S/K'_k ≤ N'_k (DO_k) gives **J'_1 = K'_k = I^{(2k)} + (e_{2k}) + M'_k**.
- **Row 0 of K_k.** π'(M_k) ⊆ π'(J_1) = R_0 = I^{(2k)} (M_k ⊆ J_1 by §2.3 of the mission; R_0 = I^{(2k)} by Corollary E1 of mission 1). So **R^K_0 = I^{(2k)}**, of colength P_{k−1} = f_{−1}: exact.
- **Row 1.** R^K_1 ⊇ J'_1, colength ≤ N'_k = f_0: exact (and R^K_1 ⊆ R_1 forces equality).
- **Rows a ≥ 2.** R^K_a ⊇ J'_1 + π'(M_k : x_{2k}^a), where π'(M_k : x_{2k}^a) is the monomial ideal generated by: (2k ∈ B) x_Cx_A^{q−1} with A ⊔ B' ⊔ C = [2k], |A| = j, |B'| = j−1; (2k ∈ C) M^{(j)}([2k]); and, for a = q−1 only, (2k ∈ A) x_Cx_{A'}^{q−1} with |A'| = j−1, |B| = j, |C| = 2k+1−2j. **The sum of colons cannot suffice for the generic rows:** the a = 1 row contains the same ideal J'_1 + π'(M_k : x_{2k}) (a ≥ 1 part), and its colength is f_0 = N'_k > f_gen. So the generic rows a ≥ 2 must contain «interaction» elements of (I + M_k) : x_{2k}^a not in (I : x_{2k}^a) + (M_k : x_{2k}^a). For k = 2 the interaction element is exactly G-a (x_0²x_1^{q−2} ∈ R_2, degree q, not divisible by any monomial of M_2 nor in K'_2).
- Consequently: **(DE_k) ⟺ [colength of R^K_a ≤ f_gen for 2 ≤ a ≤ q−2] and [≤ f_{+1} for a = q−1]**, i.e. the two even outer rows of mission 2 for the explicit ideal K_k, whose reductions to Q^gen ⊆ R^K_2 and Q ⊆ R^K_{q−1} (given D(k−2)) hold verbatim. The whole difficulty of (DE_k) is concentrated in these interaction elements, and G-a is their prototype.

### 2.2 The rows of K_k as functions on points (PROVED, given D'(k)); the exact pointwise form of G-a
Given D'(k), I = I^{(2k+1)} ⊗ F_q = gr I(Z), Z := Z_{2k+1}(F_q). For a homogeneous g of degree d and a monomial ideal N: g ∈ I + N ⟺ ∃ n ∈ N_d with g − n the top form of a polynomial vanishing on Z ⟺ g|_Z ∈ N_d|_Z + F_{d−1}, where F_e := {functions on Z given by polynomials of degree ≤ e}. Applied to N := M_k + (x_{2k}^{a+1}) and g := x_{2k}^a·m:
> **m ∈ R^K_a ⟺ (x_{2k}^a m)|_Z ∈ span((M_k + (x_{2k}^{a+1}))_{a+deg m}|_Z) + F_{a+deg m−1}.**
The monomials of M_k restrict to y_C·[y_A fully nonzero]. For G-a (k = 2, a = 2, m = x_0²x_1^{q−2}, d = q+2): the only M_2-monomials of degree q+2 are the 20 monomials x_Cx_a^{q−1} (|C| = 3), so
> **G-a ⟺ on Z_5(F_q): y_4²y_0²y_1^{q−2} ∈ span{y_C·[y_a≠0] : |C|=3, a ∉ C} + y_4³·(polynomials of degree q−1) + F_{q+1}.**
This is the statement a certificate must realize; it is the prototype of the interaction elements of §2.1.

### 2.3 What is proved for (DE_2), and the status of G-a
- **The +1 even row of K_2 is PROVED for all q:** R^K_{q−1} = π'(K_2 : x_4^{q−1}) contains e_1, x_i^q, the cubics x_ix_jx_l (x_ix_jx_l·x_4^{q−1} ∈ M_2 with C = {i,j,l}, A = {4}) and x_ix_j^{q−1} (x_ix_j^{q−1}x_4^{q−1} ∈ M_2 with C = {i}, A = {j,4}); by the count of STEP 0 (Debt 3), colength ≤ 2(3q−4) = f_{+1}. (No D'(2) needed here: the monomials are in K_2 by definition.)
- Rows 0 and 1 of K_2 are exact (§2.1). Hence **(DE_2) ⟺ [colength of R^K_2 ≤ 12(q−2)] ⟺ G-a**, because R^K_2 ⊇ (e_1, e_3, e_4, x^q) is proved (e_3 ∈ I^{(5)}; x_4e_4(x_0..x_3) = e_5 ∈ I^{(5)} ⇒ e_4 ∈ R^K_1 ⊆ R^K_2) and mission 1 §2.3(c) counts (e_1, e_3, e_4, x^q, x_i²x_j^{q−2}) to 12(q−2).
- **G-a status.** PROVED at q = 9, 27 by direct membership (`ga2.log`, `ga3.log`; the auditor also has q = 81). The certificate needs ALL of P_3, P_5, the box, at least one ε_1t and ε_1³ (`ga3.log`: dropping any class breaks it), the multipliers of P_3, P_5, ε_1³ are dense (99/52/67 terms at q = 9; 1124/924/824 at q = 27) and I found no q-symbolic shape. The reduction to a degree-(q+1) statement fails: ε_1x_0²x_1^{q−2} ∉ (P_3, e_4, x^q, ε_1^{q−1}) + (t's) (`ga2.log`), so the ε_1² factor is essential and the transfer argument of mission 2 does not apply (the fixed scheme of (P_3,P_5) is a curve of 15 lines). **The fallback «G-a alone by a q-symbolic certificate» is declared not achieved.**

STATE: NOT CONCLUDED.
Summary STEP 2: PROVED (given D'(k), D(k−1), (P_k), (DO_k)): the exact layer structure of K_k (rows 0, 1 exact; R^I_a = J'_1 = K'_k for a ≥ 1); (DE_k) ⟺ the two outer rows of the explicit ideal K_k; the sum of colons cannot give the generic rows (it would contradict row 1); the pointwise criterion m ∈ R^K_a ⟺ (x_{2k}^am)|_Z ∈ N_d|_Z + F_{d−1}; for k = 2 the +1 row is proved for all q and (DE_2) ⟺ G-a. **Missing (exact):** G-a: «x_4²x_0²x_1^{q−2} ∈ I^{(5)} + M_2 + (x_4³) in F_3[x_0..x_4] for all q» (cells q = 9, 27 true), and for k ≥ 3 the interaction elements of the generic and +1 rows of K_k (cell (3,3): the 36 quintic generators of mission 2 §1 are them).
NEXT: STEP 3.

## STEP 3
BUDGET: 40 min (start 22:52; write from 23:24). Runs: only `do2.m2` (4 variables with colons, k = 2: < 1 min, < 300 MB).

### 3.1 (DO_2) for all q: PROVED
K'_2 = I^{(4)} + (e_4) + M'_2 ⊂ S_4 = F_3[x_0..x_3], M'_2 = M^{(1)}([4]) = (x_cx_{c'}x_a^{q−1}). Rows along x_3: R'^K_a := π'(K'_2 : x_3^a) ⊂ S_3, and dim S_4/K'_2 = Σ_{a=0}^{q−1} dim S_3/R'^K_a.
- K'_2 ∋ e_1 = ε_1 + x_3 (ε_1 := e_1(x_0,x_1,x_2)), so by Debt 1 (b),(d) with ψ: x_3 ↦ −ε_1: **R'^K_a = (K̄'_2 : ε_1^a) + (ε_1)**, K̄'_2 := ψ(K'_2) ∋ ψ(e_3) = ε_3 − ε_1ε_2 = P'_3, ψ(e_4) = −ε_1ε_3, ψ(x_i^q) ∈ (y^q), and ψ(x_0x_1x_3^{q−1}) = y_0y_1ε_1^{q−1} (sign (−1)^{q−1} = 1).
- **Row 0:** R'^K_0 = π'(K'_2) = I^{(3)} + π'(M'_2) = I^{(3)} + (x_cx_{c'}x_a^{q−1} : {c,c',a} = {0,1,2}); on Z_3, x_cx_{c'} ≠ 0 forces x_a ≠ 0 (even number of nonzeros), so x_cx_{c'}(x_a^{q−1} − 1) vanishes on Z_3 and its top form lies in gr I(Z_3) = I^{(3)} (D'(1), proved). Hence R'^K_0 = I^{(3)}, colength P'_1 = f'_{−1}. [Also directly: R'^K_0 ⊆ π'(J'_1) = R'_0 = I^{(3)}.]
- **Row 1:** R'^K_1 ⊇ π'(I^{(4)} : x_3) = J_1^{(4)}, so its colength is ≤ c_1 = N_1 = f'_0 (mission 1, k = 1).
- **Generic rows 2 ≤ a ≤ q−2:** L_0 := (P'_3, ε_1ε_3) ⊆ K̄'_2 and L := L_0 + (ε_1³): as in mission 2 §2.2, R'^K_2 ⊇ (L : ε_1²) + (ε_1), whose colength is 6 by a finite q-free computation (`paso2a.log`); by monotonicity R'^K_a ⊇ R'^K_2 for a ≥ 2. So colength ≤ 6 = f'_gen(2,q).
- **Row q−1:** ε_1^{q−1}y_iy_j = ψ(x_ix_jx_3^{q−1}) ∈ K̄'_2, so y_iy_j ∈ R'^K_{q−1} for i < j ≤ 2; with ε_1 ∈ R'^K_{q−1}: y_i² = −y_i(Σ_{j≠i}y_j) + y_iε_1 ∈ R'^K_{q−1}. So R'^K_{q−1} ⊇ (ε_1, 𝔪²), colength ≤ 3 = f'_{+1}(2,q). (This replaces the transfer argument of mission 2 §2.5: for the EXPLICIT ideal the +1 row is immediate.)
- Total: dim S_4/K'_2 ≤ P'_1 + N_1 + (q−3)·6 + 3 = N'_2 (§2.5 of MISION_2: f'_{−1} = P'_1, f'_0 = N_1). ∎ Numerically the rows are {25, 24, 6×6, 3} at q = 9 and {79, 78, 6×24, 3} at q = 27, sum 88, 304 = N'_2 (`do2.log`).
Since (P_2) is empty and D(1) holds, this re-proves D'(2) through the casilla theorem: J'_1 ⊇ K'_2 and dim S/K'_2 ≤ N'_2.

### 3.2 (DO_k) for general k: the same reduction as (DE_k) (PROVED given D(k−1), D'(k−1), c_{k−1} ≤ N_{k−1})
Rows of K'_k = I^{(2k)} + (e_{2k}) + M'_k along x_{2k−1}, R'^K_a := π'(K'_k : x_{2k−1}^a) ⊂ S_{2k−1}:
- Row 0: π'(K'_k) = I^{(2k−1)} + π'(M'_k), and π'(M'_k) ⊆ I^{(2k−1)} by D'(k−1): a monomial x_Cx_A^{q−1} with 2k−1 ∈ B has |C| even, so on Z_{2k−1} with x_C ≠ 0 the number of nonzeros in A ∪ B' is odd; for j = 1 this forces x_a ≠ 0 (top form of x_C(x_a^{q−1} − 1)); for j = 2, [A fully nonzero] = 1 − x_a^{q−1} − x_{a'}^{q−1} − x_b^{q−1} on those points (top form of x_C(x_A^{q−1} − 1 + Σ_{A∪B'}x_i^{q−1})). Colength P'_{k−1} = f'_{−1}.
- Row 1: ⊇ π'(I^{(2k)} : x_{2k−1}) = J_1^{(2k)}, colength c_{k−1} ≤ N_{k−1} = f'_0.
- Given D(k−1), the layers of I^{(2k)} along x_{2k−1} for a ≥ 1 are all J_1^{(2k)} (same argument as §2.1: c_{k−1} = N_{k−1} and an increasing chain of equal colength). So for a ≥ 1: R'^K_a ⊇ J_1^{(2k)} + (e_{2k−1}(x_0..x_{2k−2})) + π'(M'_k : x_{2k−1}^a), and the a = 1 row shows this sum of colons has colength N_{k−1} > f'_gen: **the generic and +1 odd rows need interaction elements of (I^{(2k)} + (e_{2k}) + M'_k) : x_{2k−1}^a**, exactly as in §2.1. For k = 2 they are (y_1−y_2)², y_2³ (from (P'_3, ε_1ε_3) : ε_1²) and 𝔪² (from x_ix_jx_{2k−1}^{q−1} ∈ M'_2), and §3.1 closes them.
- Hence **(DO_k) ⟺ [colength of R'^K_a ≤ f'_gen for 2 ≤ a ≤ q−2] and [≤ f'_{+1} for a = q−1]**: the odd outer rows of the explicit ideal.
- Note the asymmetry with the even side: on the odd side the +1 row is free (x_Cx_{2k−1}^{q−1} ∈ M'_k gives x_C ∈ R'^K_{q−1} for |C| = 2k−2 with j = 1, and x_cx_{a}^{q−1} for j = 2), while on the even side the generic row carries the hard element (G-a).

STATE: NOT CONCLUDED (k general); CLOSED for k = 2.
Summary STEP 3: PROVED: (DO_2) for all q (§3.1); the structure of (DO_k) for all k (§3.2). Missing: the interaction elements of the odd generic rows for k ≥ 3; cell (3,3) (r'_2(3,3) = 30 = f'_{+1}; generic rows appear from q = 9: cell (3,9)).
NEXT: STEP 4.

## STEP 4 — VERDICT
STATE: CLOSED. (Start 22:46; budget 15 min.)

**Proved this turn (with proofs in this report):**
1. STEP 0 debts: odd Lemma E (Debt 1), N' and ε_1(y_i+y_j)^{q−1} ∈ N' (Debt 2), r_{q−1}(2,q) ≤ 2(3q−4) for all q (Debt 3, using U-b from the mission's §2.3).
2. **(P_k) reduced, with k as a letter, to the k-independent system (I),(II) in F_3[a,a',b,b']/(a^q,a'^q,b^q,b'^q)** (§1.1); **(P_k) for all k ≥ 3 at q ∈ {3, 9, 27}** (solutions found; gates (3,3), (4,3), (3,9) passed: `pk2.log`, `pk3.log`).
3. **Layer structure of the explicit casillas** K_k, K'_k (§2.1, §3.2): rows 0 and 1 exact; the sum of colons cannot give the outer rows; (DE_k), (DO_k) are exactly the outer rows of the explicit ideals; pointwise criterion (§2.2).
4. **(DE_2) ⟺ G-a**, with the +1 even row of K_2 proved for all q (§2.3).
5. **(DO_2) for all q** (§3.1).

**Not proved:** (a) solvability of (I),(II) for all q (hence (P_k) for q ≥ 81); (b) G-a for all q (hence (DE_2), c_2 ≤ N_2, D(2) via the chain, and everything at level 3 and above); (c) the interaction elements of the outer rows of K_k, K'_k for k ≥ 3.

**Chain (§2.4 of MISION_3) applied to what is proved:** base k = 0; level 1 (missions 1–2); level 2: (P_2) empty, D(1) ⇒ J'_1 ⊇ K'_2; (DO_2) ⇒ c'_2 ≤ N'_2 ⇒ **D'(2) for all q** (already known from mission 2, now via the casilla theorem); (DE_2) would give c_2 ≤ N_2 and D(2) — blocked by G-a. Level 3: (P_3) proved for q ≤ 27 only; blocked anyway by c_2 ≤ N_2. **CONJECTURE 1.2: NOT CLOSED.**

**Numbers, cells, logs:** calibration 8/8 (`casilla.log`); (I),(II) solvable and gates (`pk2.log`, `pk3.log`, `pk4.log` for q = 3, 9); G-a memberships (`ga2.log`, `ga3.log`); rows of K'_2 = {25,24,6×6,3} (q=9) and {79,78,6×24,3} (q=27), sums 88, 304 (`do2.log`). All runs < 30 s and < 520 MB except the killed `pk4.m2` (declared in §1.3).

**Rule incidents (declared):** `pk4.m2` exceeded 10 minutes at q = 27 and was killed; only its q = 3, 9 output is used. A first attempt of `ga2.m2` used a non-existent `timeout` binary and produced no output (rerun cleanly).

**On MISION_3.md:** no errors found. One precision: the fallback «close level 3» is unreachable without G-a, because the chain at level 3 needs c_2 ≤ N_2, which is (DE_2).
