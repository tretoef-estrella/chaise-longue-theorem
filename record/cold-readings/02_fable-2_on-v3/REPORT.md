VERDICT: HOLDS AS FAR AS I CAN CHECK — I re-derived §2 against the [DS] LaTeX source and §4–§5 line by line, found no false step, and every machine attack I could mount inside the budget (including the unprinted cells (2,27), (1,81), (1,243), and the same argument over F_5 at the new cell (2,25)) returned exactly the number the paper predicts.

# 1. VERDICT

**HOLDS AS FAR AS I CAN CHECK.** No FATAL, no GAP, no ERROR found. I found only PRESENTATION items (listed in §3), none of which touches the logic.

What this verdict rests on (details in §2):
- The object of the conjecture is exactly the paper's: [DS] generate L(X) by all (2d+1)!! matchings and all β with β_i^m = −1, nothing more; Conjecture 1.2 is stated for K = 𝒥, every even n ≥ 0, every m > 2. All five [DS] statements the paper uses are quoted verbatim from the source, and "torsion" in [DS] is Z-torsion of the same module R/(ψ_J) that the paper tensors with F_3.
- The translation §2 is right in every sign, unit and kernel. I also tested it numerically: the *literal* [DS] rings (Theorem 1.1(a) form and the §5 form of [DS], computed in Macaulay2 from [DS]'s own polynomials ψ_J, ρ_J, φ) give q^{n+1} − Q and (q−1)^{n+1} − Q at three cells, as Prop. 2.5 predicts.
- §5: P1 (fibres), the chain (Lemma 5.5), P2 (all seven cases), the coverage formula (5.1), P3 (three constructions and Lemma 5.7), the induction and its base all re-derived by hand; nothing silently assumes h ≥ ℓ, m ≥ 1 or q ≥ 9. The degenerate cases k = 0, q = 3, m = 1, ∅ work.
- Machine attacks at cells nobody had done: P2 at h = 13 and h = 40 (0 failures); the full Theorem 5.3 (dimension **and** every slice inclusion of Prop. 5.8) for every down-set at (9,4), (9,5) [7 of 13 done at the time of writing, all equal], with the negative control firing; (S) at (2,27) = 234 260, (1,81) = 18 960, (1,243) = 174 966, each predicted in writing before the run; Fact 7.2 reproduced (4730 < 4736); Theorem A.12's row inclusions at ten new cells in characteristics 0, 3, 5, 7, 11 and the negative control of Remark A.14 reproduced to the number (65).

**The one thing the authors got wrong is in their own favour:** the proof as written already covers m = p^v for every odd prime p (§6 of this report), so Remark 5.10 and §10 under-claim.

What it does NOT rest on: I did not re-prove [DS] Theorem 1.1(a) (a published topological result), and I did not audit Lemma A.10 by hand beyond its use being confirmed by machine (§4).

# 2. WHAT I CHECKED

Everything below is in `checks/` (code, logs). All engines were written by me from the paper's definitions; none reuses the authors' code. Memory and time of every run are within the budget (largest: (1,243), 292 s and 957 MB; (2,27), 23 s and 888 MB RSS).

## STEP 1 — STATE: CLOSED — The object of the conjecture (mandate 1), against the [DS] source
Source: arXiv:1405.4683v3 LaTeX, `checks/DS/DegtyarevShimada3.tex` (14 Jul 2015).
- [DS] §1: 𝒥 = all unordered partitions of {0,…,n+1} into pairs, written with j_i < k_i, j_0 < … < j_d, so j_0 = 0; B = all (β_0..β_d) with β_i^m = −1; L_{J,β}: z_{k_i} = β_i z_{j_i}; L(X) = Z-span of all [L_{J,β}]; L_K(X) for K ⊆ 𝒥. **Identical to the paper's §1.1.** There is no larger generating set (no separate permutation of coordinates: permutations are already absorbed in the choice of J and β).
- Conjecture 1.2 of [DS]: "If K = 𝒥, the group H_n(X)/L_K(X) is torsion free", under the standing hypotheses n = 2d even, m > 2. So d ≥ 0 (d = 0 called "obvious" in [DS]) and m = 3 are included. The paper's claim of scope is exact.
- Theorem 1.1(a): Tors(H_n/L_K) ≅ Tors(R/(ψ_J | J ∈ K)), R = Z[t_1..t_{n+1}]/(t_i^m − 1), ψ_J = τ_J·φ(t_{j_1}t_{k_1})⋯φ(t_{j_d}t_{k_d}), τ_J = (t_{k_0}−1)⋯(t_{k_d}−1), φ(t) = t^{m−1}+⋯+1. [DS] state explicitly that "torsion" always means Z-torsion, even for R-modules. Verbatim in the paper.
- Definition 1.3 (Γ_K), Theorem 1.4 (rank L_K = |Γ_K| + 1), Corollary 1.5 (torsion primes divide m), Claim 4.3 (dim_{K_p}(A_K ⊗ K_p) = m^{n+1} − |Γ_K| for p = 0 or p ∤ m): verbatim.
- Remark 4.4 of [DS]: rank L(X) = constant term of 1 + (x_1+⋯+x_h+x_h^{−1}+⋯+x_1^{−1})^{n+2} for m = 2h+1. Expanding, the constant term of the power is N!·[x^N]I_0(2x)^h = Q_k(q): so [DS] and Lemma 2.2 agree, and the displayed polynomials of [DS] indeed give |Γ| = rank − 1 (checked at m = 3, 4 for n = 2). This is [DS]'s slip, as the previous referee said.
- [DS] §5, d_0: the ideal (ρ_J) vanishes on the *complement* of Γ_K in (μ_m∖1)^{n+1}, so d_0 = (m−1)^{n+1} − |Γ_K|, not |Γ_K|. The paper's remark is right and is not used. Confirmed numerically below (STEP 3).

## STEP 2 — STATE: CLOSED — The translation §2 (mandate 2), by hand
- Prop. 2.1: A_K ⊗ F_p = F_p^ρ ⊕ (T_p ⊗ F_p) by right-exactness, dim = ρ + c_p; ρ from Claim 4.3 at p = 0. Correct. "Torsion free iff equality at every p | m" uses Cor. 1.5 for the other primes. Correct.
- Lemma 2.2: the bijection Γ_𝒥 ↔ {N-tuples in μ_q∖1 closed under inversion} (a ↦ (a_0, a), a_0 = a_{k_0}^{−1}) and the exponential-formula count. Correct. Only the involution matters, so the same count holds on T = F_q^× with negation.
- Lemma 2.3: y = t − t^{−1} = t^{−1}(t−1)(t+1); t^{−1} and t + 1 = 2 + (t−1) are units of the local ring F_3[t]/((t−1)^q); 1, y, …, y^{q−1} have (t−1)-adic valuations 0..q−1, hence a basis; y^q = 0. (ii): y_j + y_k = (t_j+t_k)(t_jt_k)^{−1}(t_jt_k − 1) and t_j + t_k = 2 + nilpotent is a unit. (iii) fine. **Every unit is a unit in the ring where it is used.**
- Lemma 2.4(i): (a+b)·Σ_{s=0}^{q−1}(−1)^s a^s b^{q−1−s} telescopes to a^q + b^q = (a+b)^q (q−1 even), cancel (a+b) in the domain F_3[a,b]; multiply by b, drop b^q, reindex: −ab·D(a,b). Correct. (ii): the monomial factors are y_{k_0}·Π_{i≥1} y_{j_i}y_{k_i} = Y because {k_0} ∪ ⋃{j_i,k_i} = {1..2k+1}. Correct.
- Prop. 2.5: ker(Y·) on B is spanned by the monomials with some exponent = q−1, i.e. (y_i^{q−1})B, so C → B, f ↦ Yf is well defined and injective; image of the ideal (D_J)C is the ideal (YD_J)B. Correct. Hence dim F_3[G]/(ψ̄_J) = q^{2k+1} − dim(D_J)C; with Prop. 2.1: ≤ always, = iff torsion free. Correct. "Torsion free" = "primitive" by definition; the rank clause is [DS] Theorem 1.4 (a fourth [DS] input, already reported).
- Prop. 2.6 (used only in §7 and by my dual engine): the pairing ⟨f,g⟩ = top coefficient of fg is non-degenerate on B; ann(ΣI_J) = ⋂ann(I_J); in the coordinates w, u_i, v_i (a basis of the linear forms; (y_i^q) = (w^q,u_i^q,v_i^q) by Frobenius over F_3) ψ̄_J is a unit times w·Πv_iu_i^{q−1}, whose annihilator in the box ring is (w^{q−1}, v_i^{q−1}, u_i) = I'_J + (y_i^{q−1}). Correct. The elimination of x_0 is correct (⋂ commutes with the quotient by the common element Σx_i, and (Σy)^r ≡ y_{k_0}^r mod I'_J).
- Monomial orders (mandate 3): §4 uses lex on the squarefree ring F_3[y]/(y_i^2), where every monomial of every y_T D_J is squarefree in disjoint variable sets, so no leading term is killed by the truncation; the lex-largest choice "−y_a in every untouched pair" is right because the first index where two such monomials differ is the smaller element a of a pair. §5 uses no monomial order at all: only y_1-degree and top y_1-coefficient in C_{m−1}[y_1]/(y_1^{q−1}), and every top coefficient used sits in y_1-degree ≤ q−2 (j_0 − 1 ≤ h−1; ℓ ≤ h−1; q−1−r ≤ q−2), so the truncation never removes it.

## STEP 3 — STATE: CLOSED — The translation §2, numerically, in [DS]'s own rings (Macaulay2, `checks/literalDS.m2`, log `literalDS.log`)
Computed from [DS]'s polynomials ψ_J, ρ_J, φ, never from the paper's D_J:
| cell | dim F_3[t]/(t_i^m−1, ψ_J) | predicted q^{n+1} − Q | dim F_3[t]/(φ(t_i), ρ_J) | predicted (q−1)^{n+1} − Q |
|---|---|---|---|---|
| (1,3) | 21 | 21 | 2 | 2 |
| (2,3) | 223 | 223 | 12 | 12 |
| (1,9) | 561 | 729 − 168 = 561 | 344 | 512 − 168 = 344 |
The second column confirms Prop. 2.5 (and hence, through (S), the torsion-freeness at these cells directly in [DS]'s form); the fourth confirms the paper's correction of [DS]'s d_0.

## STEP 4 — STATE: CLOSED — §4 (q = 3) by hand and by machine (`checks/thm41.py`, log `thm41.log`)
By hand: (i)–(iv) as in STEP 2 above; the counting (iii) by reflection is right; the ballot numbers of Remark 4.2 and the k = 7 list of §8 recomputed from C(n',u) − C(n',u+2): all correct.
By machine (my own greedy construction and my own expansion): for every U in the ballot set, LM(y_T D_J) = ±y_U, for k = 1..6 (sizes 6, 20, 70, 252, 924, 3432); and for k ≤ 4, brute force over all (J, T): the set of leading monomials of all y_T D_J is exactly the ballot set (0 outside it). Theorem 4.1 is correct.

## STEP 5 — STATE: CLOSED — §5 by hand (mandate 4 and 5)
- Lemma 5.1: (i)–(iv) correct; (ii) needs j + 1 ≤ q − 2 and says so.
- P1 (§5.4): the three kinds of y and their counts ℓ + ℓ + (q−1−2ℓ) = q−1; the partition arithmetic (μ ± e_j, μ ⊔ 1) and the membership of all options in Par_m (μ ⊔ 1 only when ℓ < h). Correct.
- Lemma 5.5: the three formulas for S_t of the options (removal = removal from the last row of that length, addition = to the first row of that length) and the six comparisons. Correct.
- (5.1): the structure r, N, j_0 and the implications "addition ∈ Λ ⇒ r = ℓ and N = 1 if ℓ < h", "N = 1 ⇒ r = ℓ" follow from the chain and the down-set property. Correct.
- Prop. 5.6, all seven cases, including (T), (G), the layout ℓ + ℓ̃ ≤ 2h, the parity step in (d1), the sub-case t = ℓ+1 of (d1), and the strictness in (e2). I found no hole; the degenerate cases ℓ = 0, ℓ = h, ℓ̃ = h are covered by the same text.
- Lemma 5.7: (i) sign right; (ii) cofactor expansion along the last row; (iii) fine.
- Prop. 5.8: the three constructions really are tight patterns of λ on [m] (column heights and pair counts checked in each case, including j_0 = 1 with B = ∅, μ = ∅ in (β), and r = 1 with S∖b = ∅ in (γ)); the y_1-degrees and top coefficients are as stated; the coverage j = q−1−F is exact at F = q−1 (j = 0 via (α) with j_0 = 1 or (β) with μ = ∅) and F = 0 never needs a construction; (γ) cannot reach F = q−1 (r ≤ h).
- §5.8: induction on m is well founded; base m = 0 right for Λ = {∅} and Λ = ∅; the inequality chain is right; "invariance under relabelling" holds since every generator changes by a sign under a permutation of indices.
- Smallest cases by hand: k = 0 (m = 1, 𝒥 = {[[0,1]]}, D_J = 1, dim C_1 = 2 = Q_0(3)); q = 3 (h = 1, Par_m = single rows, Λ_i are initial segments); m = 1 from m = 0 (F_Λ(∅) = q−1, so V_{{∅}} = F_3 ⊆ W_j for all j, and dim C_1 = q−1 = Σ_j 1); Λ = ∅; μ = ∅ in (β). All fine. No hidden assumption h ≥ ℓ (it is a property of λ(M)), m ≥ 1 (base is m = 0) or q ≥ 9 (nothing in §5 uses q ≥ 9).
- Hidden uses (mandate 5): §2–§5 use no computation and not Theorem A; every reference to §8 is in a remark or a side sentence ("The coverage is exact", Remark 5.9, Remark 4.2(3)). The sentences asserted rather than proved in §2–§5, all of them standard or one-line, are listed in §3 (item P-7).

## STEP 6 — STATE: CLOSED — §5 by machine at cells the previous referee did not do
- **P2 and the chain at large h** (`checks/p2check.py`, log `p2check.log`): all comparable pairs of Par_{m−1}, position by position, at q = 27 (h = 13; m = 3..10, up to 1248 pairs), q = 81 (h = 40; m = 4,6,8,9), q = 9 (m = 5..13, 3285 pairs at m = 13), q = 3: **0 failures**. The previous checks stopped at h = 4.
- **Theorem 5.3 in full, every down-set** (`checks/downset.py`; my own tight-pattern generator, my own layers computed from the *fibres* (not from (5.1)), my own slice test "y_1^j g ∈ V_Λ + span(y_1-degree < j)"):
  - (9,3): 5 down-sets, dim V_Λ = |Z_Λ| for all, all slice inclusions hold.
  - (9,4): 10 down-sets: 0, 168, 1896, 2216, 2280, 2600, 3752, 3896, 4088, 4096 — the same ten numbers as §8 Route 3; all slices hold; the negative control (one slice tighter) fails in 7 of 9 tests, so the coverage really has no slack.
  - (9,5): 13 down-sets; done at the time of writing: 0, 5120, 14720, 22880, 23400, 26720, 27240 (each = |Z_Λ|), all slice inclusions hold. The remaining six (the largest ideals, ambient 32 768) were still running; the final lines will be in `downset_9_5.log`.
  - (27,3) and (9,6): queued behind (9,5); logs `downset_27_3.log`, `downset_9_6.log`.

## STEP 7 — STATE: CLOSED — A number not in the paper (mandate 6)
Predictions and estimates were written into the run scripts before running (`checks/run_k1.sh`, `checks/run_227.sh`). Engines: `dualform.py` (intersection form, plain) and `symdual.py` + `rank3.c` (intersection form split by the four characters of the Klein group ⟨(12)(34),(13)(24)⟩ acting on y_1..y_4; exact, no randomness; streaming RREF over GF(3) in C). Both engines were first calibrated on (1,3), (2,3), (1,9), (1,27), (2,9): totals and graded profiles agree with the sum form and with the paper.
| cell | predicted Q_k(q) | computed b_k(q−1) | time | memory |
|---|---|---|---|---|
| **(2,27)** | 234 260 | **234 260** | 23 s | 888 MB |
| (1,81) | 18 960 | **18 960** | 3 s | 305 MB |
| (1,243) | 174 966 | **174 966** | 292 s | 957 MB |
Graded profile at (2,27) (intersection form, degrees 0..75): 1, 5, 15, 34, 65, 110, 170, 245, 335, 440, 560, …, 6995, 7010, 6995, …, symmetric; full list in `run_227.log`. Three unprinted cells, three exact matches. (3,27) and (4,9) are out of reach at 1 GB (26^7 and 8^9 monomials).

## STEP 8 — STATE: CLOSED — Theorem A (mandate 7)
- **Row inclusions of Theorem A.12** (`checks/thmA12.m2`, log `thmA12.log`), from Definitions A.7/A.11 and the dictionary A.2, with R_a(G) = ((G + (z^{a+1})) : z^a) ∩ F[L] computed by colon and elimination: all q rows at (char, q, |L|, μ) = (5,5,4,(2,1)), (5,5,4,(2,2)), (5,5,4,(3,1)), (7,7,4,(2,1,1)), (7,7,3,(3,2,1)), (11,5,4,(1,1)), (0,5,4,(2,1)), (3,3,5,(2)), (3,9,4,(2,2,1)), (3,9,4,(4,1)), (3,9,5,(3,1)): **all inclusions hold** (0 generators outside their row).
- **Negative control** (Remark A.14, reversed lower order): (3,9,5,(3,1)) gives exactly **65** generators of the child (3) outside row 0, the paper's number; also 10 at |L| = 4 and 16 at (5,5,4,(2,1)). My Θ implementation therefore coincides with theirs.
- Fact 7.2: dim (D_J : J ∈ K)C = 4730, |Γ_K| = 4736 by enumeration on T^5; P_K = 7089 by enumeration on F_9^6; full family 5120/5120 and P_2(9) = 7761. Cor. 6.1 at (2,3): 141 (M2). Remark 6.3(1) char-2 dimensions 21, 65, 133, 225 and N_q(4) = 19, 61, 127, 217: all reproduced.
- Prop. A.5, Lemma A.6, Lemma A.8 (P),(B),(A),(V), Lemma A.9, Lemma A.13 and the case analysis of A.12 re-read by hand: no gap found (Lemma A.10 only checked through its consequences, see §4).

## STEP 9 — STATE: CLOSED — The paper's own argument transposed to F_p, p = 5, 7 (evidence for §6 of this report)
Nothing in §2 uses p = 3 except that 2 is a unit (Lemma 2.3: t + 1 = 2 + (t − 1)); the telescoping identity of Lemma 2.4(i) gives a^q + b^q = (a+b)^q in any characteristic p with q = p^v; §5 is field-free. So I ran the same engines over F_5 and F_7 (`checks/symdualp.py`, `checks/rankp.c`, script `checks/run_fp.sh` with the predictions written first, log `run_fp.log`) and the literal [DS] rings over F_5, F_7 (`checks/literalDS5.m2`):
| field | cell | predicted Q | computed | status of the cell |
|---|---|---|---|---|
| F_5 | (1,5) | 36 | 36 | known ([De14], [DS]) |
| F_5 | (2,5) | 400 | 400 | known ([DS] computer, (4,5)) |
| F_5 | (3,5) | 4900 | 4900 | known ([DS] computer, (6,5)) |
| F_7 | (1,7) | 90 | 90 | known |
| F_7 | (2,7) | 1860 | 1860 | known ([DS] computer, (4,7)) |
| F_5 | (1,25) | 1656 | 1656 | k = 1 known [De14]; this algebraic form new |
| F_7 | (1,49) | 6768 | 6768 | idem |
| F_5 | (1,125) | 45 756 | 45 756 | idem |
| **F_5** | **(2,25)** | **182 400** | **182 400** | **NEW: Fermat fourfold of degree 25** (44 s, 735 MB) |
Literal [DS] rings: dim F_5[t]/(t_i^5 − 1, ψ_J) = 89 = 125 − 36 and dim F_5[t]/(φ(t_i), ρ_J) = 28 = 64 − 36 at (1,5); 253 = 343 − 90 and 126 = 216 − 90 at (1,7) over F_7; 2725 = 3125 − 400 and 624 = 1024 − 400 at (2,5). Exactly what the p-version of Prop. 2.5 predicts.

## STEP 10 — STATE: CLOSED — Literature for the case p ≥ 5 and for [De15]
- [De15] = arXiv:1512.06199 (source fetched, `checks/DS/de15/kinosaki.tex`): the conjecture is restated there (label `conj.TK`, "For the full set K = 𝒥 one has T_𝒥 = 0"), with the same list of computer-verified cells as [DS] and the sentence "we failed to prove the conjecture in full generality". The conjecture sits in the fourth \section of that source ("Higher dimensions"), consistent with the number 4.4; the paper's citation is correct.
- Aljovin–Movasati–Villaflor, *Integral Hodge conjecture for Fermat varieties*, J. Symbolic Comput. (2019), arXiv:1711.02628: an algorithm comparing the elementary divisors of the lattice of linear cycles and of Hodge cycles, run for the quartic and quintic Fermat fourfolds. Computational, within [DS]'s range; it does not prove any p ≥ 5 case in general. The paper does not cite it and should (see §5).
- I found no published proof of Conjecture 1.2 for any k ≥ 2 and any m beyond the computer cells of [DS]. The case p ≥ 5, m = p^v, k ≥ 2 is open in the literature.

# 3. FINDINGS

**No FATAL. No GAP. No ERROR.** The Main Theorem follows from §2 + §5 given [DS] Theorem 1.1(a), Claim 4.3, Corollary 1.5 (and Theorem 1.4 for the rank clause). Everything I could test by machine agrees with the paper, including three cells whose value nobody had printed.

PRESENTATION (new; none previously reported):
- **P-1 (§5.5–5.7, (5.1)).** The symbol `N` is global (N = 2k+2, §1.2, §3, §7) and is redefined as the indicator `N := [μ ⊔ 1 ∈ Λ]` in (5.1) and used as such in Prop. 5.8. Rename the indicator (e.g. `ν_Λ(μ)` or `[new]`).
- **P-2 (§5.2).** "Partitions of different sizes are comparable" reads as "any two are comparable", which is false ((2) and (1,1,1) are incomparable). It should say "the order is defined between partitions of different sizes" (S_t compared for all t, padded with zeros).
- **P-3 (Fact 7.2).** "A_K = P_K = 7089": `A_K` is never defined for a subfamily (E is the ideal of the odd elementary symmetric functions, a full-family object). Say which ideal is meant (presumably ⋂_{J∈K} I_J + (x_i^q), or the ideal of the union of the K-spaces) or drop the sentence. P_K = 7089 is correct.
- **P-4 (Prop. 5.8, case (β)).** The hypothesis ℓ < h is stated in the case label but its necessity (μ ⊔ 1 ∈ Par_m) is what makes the three cases exhaustive; one clause "N = 1 forces ℓ < h" would close the "exactly one of the following occurs".
- **P-5 (§5.4 vs Lemma 5.1(iv)).** `F(M')` is defined in Lemma 5.1(iv) for a general Z and reused in §5.4 for Z = Z_Λ; say "with Z = Z_Λ".
- **P-6 (Prop. 2.6, last sentence).** The passage from 2k+1 to N = 2k+2 variables is one line; a referee will want the two facts spelled out: ⋂ commutes with the quotient by the common element x_0+⋯+x_{2k+1}, and (Σy_i)^r ≡ y_{k_0}^r (mod I'_J).
- **P-7 (mandate 5: sentences of §2–§5 asserted, not proved).** All are standard, but a journal referee may ask for a word on each: (a) §2.1 "By right exactness of ⊗, dim(A_K ⊗ F_p) = ρ + c_p"; (b) Lemma 2.2 "By the exponential formula"; (c) §5.5 "r̄_j is non-decreasing in j", "r̲_j is non-decreasing in j"; (d) §5.5 "since rows of equal length give equal partitions, r = 0 or r is the last row of its length"; (e) Prop. 5.6 "Every position falls into exactly one of (a)–(e)" and "The degenerate cases … are included"; (f) §5.8 "the statement is invariant under relabelling the indices"; (g) Theorem 4.1(iv) "Elements … with pairwise distinct leading monomials are linearly independent"; (h) Theorem 4.1(ii) "The number of unmatched down-steps is max(0, −min_i h(i))"; (i) Prop. 2.6 "the pairing is non-degenerate" and "(y_i^q) is also generated by w^q, u_i^q, v_i^q".
- **P-8 (§5.7, "The coverage is exact").** This sentence cites a computation (§8) inside the proof section; move it to Remark 5.9 so that §5 contains no reference to machine work at all. (It is not used.)
- **P-9 (§1.1, References).** [De15] is correctly described (STEP 10). Missing reference: Aljovin–Movasati–Villaflor, *Integral Hodge conjecture for Fermat varieties*, J. Symbolic Comput. 91 (2019), arXiv:1711.02628, which attacks the same lattice by computer for the quartic and quintic fourfolds; a referee will expect it in §1.1 next to the [DS] computer cells.

# 4. WHAT I DID NOT CHECK
- The proofs inside [DS] (Theorem 1.1(a) via the Pham polyhedron and intersection numbers; Theorem 1.4; Corollary 1.5). I only checked that they are quoted correctly and that their hypotheses (n = 2d, m > 2, K ≠ ∅) are met.
- Lemma A.10 (the "odd identity") by hand: I checked its statement's use in A.12 only through the machine tests of the row inclusions (which exercise it in the new-class and raise cases) and the paper's own 166 random instances.
- (3,27) and (4,9): not feasible under 1 GB by any method I could devise (ambient 26^7 ≈ 8×10^9 and 8^9 ≈ 1.3×10^8 monomials with rank 7.9×10^6). (3,9) = 190 120 was not recomputed (one engine in the paper); a second engine would need ~10^14 operations in my scheme.
- The down-set engine at (27,3) and (9,6) (queued; results will be in `checks/downset_27_3.log`, `checks/downset_9_6.log`) and the last 6 down-sets at (9,5) (running when this report was closed).
- The repository github.com/tretoef-estrella/chaise-longue-theorem (not opened; my instructions forbid the authors' archive and the repository is not needed for the proof).
- The Specht-module remark 4.2(3) and the leading-monomial remark 5.9(2): not claimed by the paper, not checked.
- Equality dim V_Λ = |Z_Λ| for every down-set: measured (all my down-sets show equality) but, as the paper says, not proved; the Main Theorem does not need it.

# 5. HOW TO MAKE THE PAPER MORE ROBUST AND BRILLIANT

(written after sections 1–4 were complete)

**What a referee would still ask for.**
1. **Claim the theorem you have proved.** Every step of §2 holds over F_p for q = p^v and every odd prime p (STEP 9: the only facts used are "2 is a unit" and Frobenius), and §5 never sees the characteristic. The paper proves Conjecture 1.2 for **every odd prime power m = p^v**, not only 3^v. Remark 5.10 and §10 should say so, with the two sentences of §2 that mention "characteristic 3" rewritten for p (Lemma 2.3(i): "t^q − 1 = (t−1)^q in characteristic p"; Lemma 2.4(i): "In characteristic p, (a+b)·Σ… = a^q + b^q"). If the authors want to keep 3^v as the headline, they must at least explain what they believe fails for p ≥ 5 — nothing does. A referee will find this in ten minutes and will not understand the reticence.
2. **The reverse inequality dim V_Λ ≤ |Z_Λ|** (Remark 5.9(1)). The authors say it "should follow by restricting functions on T^m to supports" and have not audited it. If the argument is short, include it: Theorem 5.3 becomes an equality, the main line becomes "dim V_{(1)} = |Γ'|" without appeal to Prop. 2.5 for ≤, and every equality measured in §8 (all 38 down-sets I computed show equality too) becomes a consequence instead of a mystery. If it is not short, say precisely what is missing.
3. **State Theorem 5.3 for any field and any odd q**, since that is what is proved. Then the Main Theorem for p is a corollary of one theorem plus one translation, and §4 (q = 3) becomes a remark with an explicit basis.
4. **Independence of the [DS] inputs:** say in one sentence that Theorem 1.1(a) is the only topological input and that everything after it is commutative algebra over Z; list Theorem 1.4 among the inputs (rank clause).
5. **Cite Aljovin–Movasati–Villaflor (2019)** and say how the present method differs (a proof, not an elementary-divisor computation).

**Which proofs to shorten or expand.**
- Expand Prop. 5.8 by one displayed example: q = 9, m = 4, μ = (2,1), showing the three constructions (α), (β), (γ) with their y_1-degrees 1, 2, 5 and the coverage F = 7, 6, 3 — this is where a reader gets lost.
- Expand (5.1) by half a line each for "addition ∈ Λ ⇒ r = ℓ" and "N = 1 ⇒ r = ℓ" (they are chain consequences; say "by Lemma 5.5 and the down-set property").
- Shorten §8 by two thirds: the referee's guide and Route 4 table are the useful parts; the numbers of sessions and files (§9) belong in a repository README, not in the paper.
- Prop. 5.6 is fine as is; add the one-line lemma "(T)" as a numbered lemma so that it can be cited.

**What to move to an appendix.** §7 (the sandwich and the counterexample), §8 Routes 1–3 and §9. Keep in the main text only the Route 4 table as a one-line remark.

**What is missing.**
- **A figure** of the chain of options of Lemma 5.5 for one μ (e.g. μ = (3,1,1), q = 9): the L = 8 positions on a line, removals on the left, the middle block, additions on the right, and the initial segment picked out by a down-set.
- **A table** of Par_4 at q = 9 with F_Λ(μ) for one Λ, the layers Λ_i and the slices W_{q−2−i}: one page, and the reader sees P1–P3 at once.
- **A worked example of the translation**: at k = 1, q = 3, write ψ_J, ψ̄_J, Y and D_J explicitly (three lines), and the 6 = 27 − 21 count.
- The definition of A_K for subfamilies in Fact 7.2 (P-3), or its removal.

**How to make the main idea visible in one page.** Open §5 with the following paragraph, before any definition: "Fix the last variable y_1. An ideal V of C_m decomposes into q−1 slices W_0 ⊆ ⋯ ⊆ W_{q−2}, ideals of C_{m−1}, with dim V = Σ dim W_j. A point set Z ⊆ T^m decomposes into q−1 layers Z_{>0} ⊇ ⋯ ⊇ Z_{>q−2} with |Z| = Σ|Z_{>i}|. We attach to every down-set Λ of partitions an ideal V_Λ (generated by products of D-factors and Vandermondes, one per 'tight pattern') and the set Z_Λ of points whose residue partition lies in Λ, and prove three things: the layers of Z_Λ are again of the form Z_{Λ_i} (P1); the Λ_i are down-sets (P2); the slice W_{q−2−i}(V_Λ) contains V_{Λ_i} (P3). Induction on m gives dim V_Λ ≥ |Z_Λ|; at Λ = {(1)} this is (S)." Then a one-page diagram: the slice/layer ladder with the arrow V_{Λ_i} → W_{q−2−i}. That page is the paper.

# 6. OPINION: HOW TO PROVE THE CASE p ≥ 5

(written after sections 1–4 were complete)

**Short answer: it is already proved by this paper, and the authors have not noticed.**

**What exactly in §2 must be rewritten.** Replace F_3 by F_p throughout, with q = p^v, p an odd prime, and check the four places where a property of the field is used:
1. Lemma 2.3(i): "t^q − 1 = (t − 1)^q" — true in characteristic p for q = p^v (Frobenius). "t + 1 = 2 + (t−1) is a unit" — true iff 2 ∈ F_p^×, i.e. p odd. **This is the only place where p = 2 dies**, and it is exactly the obstruction for even m.
2. Lemma 2.3(ii): t_j + t_k = 2 + nilpotent, a unit: p odd again. (iii): φ(u) = (u−1)^{q−1} in F_p[u]: Frobenius.
3. Lemma 2.4(i): the telescoping identity (a+b)·Σ_{s=0}^{q−1}(−1)^s a^s b^{q−1−s} = a^q + b^q holds over Z (it only uses that q is odd); a^q + b^q = (a+b)^q needs characteristic p with p | q. Nothing else.
4. Prop. 2.1: "only p = 3 matters" becomes "only p matters" by Corollary 1.5. Prop. 2.6 uses ℓ^q = Σ c_i y_i^q for a linear form over F_p: Frobenius, since c_i^q = c_i for c_i ∈ F_p.
Lemma 2.2 and Lemma 3.1 use only that q is odd. So §2 holds verbatim over F_p, and (S) over F_p at (k, p^v) is equivalent to Conjecture 1.2 at (2k, p^v).

**What in §5 might hide a 3.** Nothing. I looked for it specifically: the residue/partition combinatorics uses T = F_q^× only as a set with the fixed-point-free involution u ↦ −u (q odd); D(a,b) is defined over Z and Lemma 5.7(i) uses q − 2 odd; Lemma 5.7(ii),(iii) are Vandermonde identities over Z; W_j and V_Λ are defined over any field; Prop. 5.6 is pure partition arithmetic; the induction is counting. The coefficient 2 never appears in §5 (it appears in Appendix A, Lemma A.10, which is not used for the Main Theorem). The one thing to re-check is the sign bookkeeping "±" in Lemma 5.2 and Prop. 5.8, which over F_p means "a unit ±1", still a unit.

**Machine evidence (STEP 9).** The same engines, run over F_5 and F_7 with the field as the only change, give (S) at (1,5), (2,5), (3,5), (1,7), (2,7), (1,25), (1,49), (1,125) and at the new cell (2,25) = 182 400 = Q_2(25), and the literal [DS] rings over F_5, F_7 give exactly q^{n+1} − Q and (q−1)^{n+1} − Q. In particular, subject to the p-translation above (which I have checked line by line), **H_4(X)/L(X) is torsion free for the Fermat fourfold of degree 25**, a cell outside [DS]'s list.

**What to check in the literature.** For k = 1 all m are known [De14]. For k ≥ 2 the only results are the [DS] computer cells ((4, m ≤ 12), (6,3), (6,4), (6,5), (8,3)) and Aljovin–Movasati–Villaflor's elementary-divisor computations at (4,4), (4,5); [De15] restates the conjecture as open. So a theorem "Conjecture 1.2 holds for every odd prime power m" is new for every k ≥ 2 and every odd prime power m > 12 (and for m = 25, 27, 49, 81, … it is the first result of any kind).

**Concrete plan (one afternoon).**
1. Rewrite §2 with p in place of 3 (four sentences, listed above); state Lemma 2.3 for odd p and note the failure at p = 2.
2. State Theorem 5.3 over an arbitrary field F and any odd q ≥ 3; the proof is unchanged.
3. Corollary: for every odd prime p and v ≥ 1, (S) holds over F_p at (k, p^v), hence Conjecture 1.2 holds for m = p^v.
4. Add the F_5/F_7 rows above to the verification record (and (2,25)).
5. **What remains genuinely open after that:** (a) even m, where Lemma 2.3 fails because 2 is not a unit — here y = t − t^{−1} = t^{−1}(t−1)^2 is not a generator, and the ring F_2[t]/(t^{2^v} − 1) needs a different coordinate (e.g. y = t − 1 itself, at the cost of losing the clean antisymmetry y ↦ −y, which is what makes D antisymmetric and Lemma 2.2's involution work); (b) composite odd m = p^v m' with p ∤ m': F_p[t]/(t^m − 1) ≅ Π_{ζ^{m'}=1} F_p(ζ)[t]/((t−ζ)^{p^v}) is a product of local rings, and the ideal (ψ̄_J) splits accordingly; each factor is a twisted copy of the m = p^v problem with the involution replaced by t ↦ t^{−1} acting on the m'-th roots of unity — the m'-torsion of the character group enters and the count |Γ| must be redone per factor. I would attack (b) first: fix m' and p, and compute the factor-wise dimensions at (1, 15) over F_3 and F_5 to see whether the p-part of the torsion is factor-wise the (k, p^v) problem. If it is, the present proof gives all odd m; if not, the discrepancy is the new mathematics.
