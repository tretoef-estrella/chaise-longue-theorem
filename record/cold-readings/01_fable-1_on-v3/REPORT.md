VERDICT: HOLDS AS FAR AS I CAN CHECK — I re-derived §2 against the LaTeX source of [DS] arXiv:1405.4683v3 symbol by symbol, re-derived every lemma, all seven cases of Proposition 5.6, the three constructions of Proposition 5.8 and the induction of §5 by hand, re-derived Appendix A by hand, and ran my own independent code (no code of the authors was used) against every checkable numerical claim; I found no FATAL error and no GAP, only presentation-level remarks.

## VERDICT
**HOLDS AS FAR AS I CAN CHECK.** The Main Theorem follows from (i) three results of [DS] that I verified are quoted correctly, (ii) the translation §2, which I re-derived line by line, and (iii) Theorem 5.3, whose proof (P1, Chain, P2 with its seven cases, P3 with its three constructions, and the induction) I re-derived by hand and could not break. The specific attack the authors invite — long, very uneven partitions at q=3 (h=1) and q=9 (h=4) where ℓ hits the cap h — was carried out exhaustively by machine (every comparable pair of Par_{m−1} up to m=16 at q=3 and m=14 at q=9): 0 failures. Theorem A (Appendix A) is independent of the Main Theorem, is not used by it, and its proof also holds as far as I can check. No computation I ran contradicts any stated claim; every number I recomputed (25 cells of (S)/down-sets/Theorem A/Fact 7.2/the table of §3) agrees with the paper.

Caveat that a human expert must still weigh: the proof rests on [DS, Theorem 1.1(a)], [DS, Claim 4.3] and [DS, Corollary 1.5]. I verified that they are quoted exactly; I did **not** re-prove them (see WHAT I DID NOT CHECK).

## WHAT I CHECKED

### §2 against the original [DS] (arXiv:1405.4683v3, LaTeX source downloaded from arXiv e-print)
- Conventions: [DS] eq. (1.1)/(eq:condJ) requires `j_0<...<j_d`, and the text says "(Note that we always have j_0=0)". ✓ as quoted.
- `t_0`: [DS] defines Λ = Z[t_0^{±1},…,t_{n+1}^{±1}]/(t_0⋯t_{n+1}−1) = Z[t_1^{±1},…], so `t_0 = (t_1⋯t_{n+1})^{-1}`; R = Z[t_1..t_{n+1}]/(t_i^m−1). ψ_J = τ_J·φ(t_{j_1}t_{k_1})⋯φ(t_{j_d}t_{k_d}) with τ_J = Π_{i=0}^d (t_{k_i}−1). Since j_0=0 and k_0≥1, no t_0 appears in ψ_J. ✓
- φ(t) = t^{m−1}+⋯+1 ✓. Definition 1.3 (Γ_K) ✓ verbatim. Theorem 1.1(a): torsion of H_n(X)/L_K(X) ≅ torsion of R/(ψ_J | J∈K) ✓ (Z-torsion, per [DS]'s own convention). Theorem 1.4: rank L_K = |Γ_K|+1 ✓. Corollary 1.5 ✓ verbatim. Claim 4.3 (label claim:Kp, third numbered item of §4 after Lemma 4.1 and Claim 4.2): "If p=0 or (p,m)=1 then dim_{K_p}(A_K⊗K_p) = m^{n+1}−|Γ_K|", K_p algebraically closed of char p ✓ verbatim.
- Numbering: sections of [DS] are 1 Intro, 2 Outline, 3 Intersection, 4 R-submodule, 5 Computational criterion; theorem-type environments share one counter, so Claim 4.3, Remark 4.4, Lemma 4.5 are as cited ✓.
- Remark 4.4 of [DS]: the display for n=2 is `3m²−9m+6+δ_m`. At m=3 this gives 6, but rank L(X)=7 for the cubic surface (Picard rank 7). So the display prints |Γ|, not rank; the paper's "external check" remark is correct.
- Lemma 2.3 (i)(ii)(iii): re-derived. Units: t, t+1=2+(t−1), t_j+t_k=2+(t_j−1)+(t_k−1) are units (nilpotent + unit, 2∈F_3^×) ✓. y=t^{-1}(t−1)(t+1) ✓. (ii) identity y_j+y_k=(t_j+t_k)(t_jt_k)^{-1}(t_jt_k−1) expanded and checked ✓.
- D(a,b): (a+b)·D = b^{q−1}−a^{q−1} by telescoping, using q−2 odd ✓; antisymmetry ✓.
- Lemma 2.4(i): (a+b)·Σ_{s=0}^{q−1}(−1)^s a^s b^{q−1−s} = b^q+a^q (q−1 even) ✓; multiply by b, drop b^q, reindex ✓ gives −ab·D(a,b) ✓. (ii) monomial bookkeeping {k_0}∪⋃{j_i,k_i} = {1..2k+1} ✓.
- Proposition 2.1: ρ = m^{n+1}−|Γ_K| from Claim 4.3 at p=0; dim_{F_p} = ρ + c_p ✓; direction of inequality ≥ ✓.
- Proposition 2.5: kernel of Y· on B is (y_i^{q−1}) ✓; so dim(ψ̄_J)B = dim(D_J)C ✓; hence dim(D_J:J∈K)C ≤ |Γ_K| (direction re-derived from Prop 2.1) ✓ and "≥ suffices" ✓.
- Lemma 2.2 and Lemma 3.1 (bijections, exponential formula, Q_1(q)=3q²−9q+6, Q_k(3)=C(2k+2,k+1)) ✓ re-derived.

### §5, by hand
- Lemma 5.1 (i)–(iv): re-derived; (ii) needs j+1 ≤ q−2, stated ✓.
- Lemma 5.2: (1) is the only λ ≼ (1) of odd size ✓; tight patterns of (1) ↔ matchings ✓; Z_{(1)} = Γ' ✓.
- §5.4 (P1): the q−1 values y split as ℓ (removals) + ℓ (additions) + 2(h−ℓ) (new class) ✓; F(M') depends only on μ ✓; all options lie in Par_m ✓.
- §5.5 (Chain), Lemma 5.5: S_t of the three moves ✓; r̄_j, r̲_j monotone in j ✓; μ⊔1 ≼ μ+e_ℓ via r̲_ℓ ≤ ℓ ✓; degenerate ℓ=0, ℓ=h ✓. Formula (5.1) ✓ (also checked by machine against the direct count, see below).
- Proposition 5.6 (P2), all seven cases re-derived: (a) contradiction at S_{p−1} ✓; (b) contradiction at S_j ✓; (c) via (5.2) ✓; (d1) four sub-cases incl. t=ℓ+1 with μ̃_{ℓ+1}=1 forcing row ℓ+2 of length 1 ✓; (d2) ✓; (e1) transitivity ✓; (e2) uses μ̃_j=0 ✓. Position layout: removal(μ) vs addition(μ̃) impossible because ℓ+ℓ̃ ≤ 2h=L ✓; all combinations covered ✓.
- Lemma 5.7 (i) sign (−1)^{q−2−t}=(−1)^{t+1} since q−2 odd ✓; (ii) Laplace expansion of Vandermonde along last row ✓; (iii) ✓.
- Proposition 5.8: (α) column μ_{j_0}+1 has height j_0−1 ✓, degree j_0−1, F=q−j_0 in both sub-cases ✓; (β) degree ℓ, F=q−1−ℓ ✓, μ=∅ ✓; (γ) the pattern of λ=μ−e_r has one more pair ✓, degree ≤ q−1−r with top coefficient ±G by Lemma 5.7(i)(ii) ✓. Trichotomy (α)/(β)/(γ) exhaustive given F ≥ 1 ✓.
- Induction (§5.8): base m=0 ✓; step uses Lemma 5.1(iii), Prop 5.8, IH on Λ_i ⊆ Par_{m−1} (a down-set by P2), Lemma 5.1(iv) and Z_{>i}=Z_{Λ_i} ✓.
- Corollary 5.4 / Main Theorem: (S) ⇐ Theorem 5.3 at root + Prop 2.5 ✓. Appendix A / Theorem A is not invoked anywhere in §2–§5 ✓ (checked by reading every cross-reference).

### Machine checks (my own code, in `checks/`; none of the paper's code was used)
- `p2test.py`: Proposition 5.6 tested on **every** comparable pair of Par_{m−1}: q=3 (m ≤ 16), q=9 (m=3..14, e.g. 4629 pairs at m=14), q=27 (m ≤ 11), q=81 (m ≤ 9). Also Lemma 5.5 (chain) and "options ∈ Par_m". **0 failures.**
- `sform.py` + `ideal.py` (graded row-echelon over F_3, dense numpy): dim (D_J)C = 6, 20, 70, 252 at (k,3), k=1..4; 168 at (1,9); 1950 at (1,27); **5120 at (2,9)** with graded ranks 15,45,90,150,224,310,395,470,515,530,516,475,411,329,245,170,110,65,34,15,5,1 — identical to the paper's Route 4 table.
- `downset.py`: Theorem 5.3 for **every** ≼-down-set at (q,m) = (3;3,4,5), (9;2,3,4): dim V_Λ = |Z_Λ| in every case (e.g. at (9,4): 0,168,1896,2216,2280,2600,3752,3896,4088,4096). 0 violations.
- `p3test.py`: Proposition 5.8 tested directly: for every down-set at (3;3,5), (9;2,3), every i and every tight-pattern generator of Λ_i, membership in the slice W_{q−2−i}(V_Λ) computed by linear algebra: **0 failures**; (5.1) agrees with the direct option count; Λ_i is a down-set in every case. Negative control: tightening by one slice fails in 2/6, 36/93, 2/15, 8/82 generator tests — so my test is sensitive.
- `thmA.py`: dim F_p[x_1..x_n]/(e_odd; x_i^q) for p ∈ {3,5,7}, q ∈ {1,3,5,7,9}, n ≤ 4 equals N_q(n) in all 75 cells; for p=2 it fails at n=4 (21,65,133,225 vs 19,61,127,217), exactly as Remark 6.3(1) states.

## FINDINGS
No FATAL. No GAP. No ERROR affecting any statement. Presentation-level remarks only:

1. **PRESENTATION — §10 / §1.2 / Main Theorem, last clause.** §10 says the Main Theorem is proved "modulo three published results of [DS]" (Theorem 1.1(a), Claim 4.3, Corollary 1.5). The torsion-freeness is; but the clause "L(X) is a primitive sublattice of rank Q_k(3^v)+1" in the Main Theorem also uses [DS, Theorem 1.4] (rank L_K = |Γ_K|+1) together with Lemma 2.2. Theorem 1.4 is cited in §1.2 but not listed among the inputs in §2 or §10. Harmless (Theorem 1.4 is proved in [DS] from the same Claims 4.2–4.3), but the count of inputs should be four, or the rank clause should be attributed to §1.2.

2. **PRESENTATION — Abstract, last sentence of paragraph 2.** "for proper subfamilies the analogous statement is false" reads as "for every proper subfamily". §7 shows it is false for *some* proper subfamilies (my recount at q=3, k=2: 800 of the 32 767 non-empty subfamilies fail, the others satisfy equality; at q=9, k=2 the 13-matching family of Fact 7.2 fails). Suggest "for some proper subfamilies".

3. **PRESENTATION — Corollary 6.2.** "the torsion subgroup … is a 2-group, and its rank is N_q(n)": "its" grammatically refers to the torsion subgroup (rank 0). Intended: the rank of the group M = Z[x_1..x_n]/(e_j: j odd; x_i^q) is N_q(n).

4. **PRESENTATION — Lemma A.13(ii) vs its use.** (ii) is stated under the standing hypothesis s ≥ 1, but in the proof of Theorem A.12 (raise case, i < i*) and in (ii)'s own proof, terms with level ≤ 0 are needed and are handled by (V). The proof is correct, but (ii) would read more cleanly if stated for all s ∈ Z with "generator or in box by (V)" built in, as its proof already does.

5. **PRESENTATION — Remark after Proposition 2.5, item (2), about [DS, §5].** The paper is right that [DS, §5] write "d_0 = |Γ_K|" whereas the correct value is (m−1)^{n+1} − |Γ_K| (I re-derived it: by [DS, Lemma 4.5], at points with all coordinates ≠ 1, ρ(x,y)=0 iff xy ≠ 1, so V(ρ_J : J∈K) is the *complement* of Γ_K in (μ_m∖{1})^{n+1}). This is a slip in [DS], not in the paper; it does not affect the criterion d_0 = d_p. Recording it here so that a reader does not count it against the paper. (Consistent with the paper's own May-2026 number 1124 = 2^{11} − 924 at (10,3).)

6. **PRESENTATION — §2.2 "External check".** Correct as stated: the displays of [DS, Remark 4.4] evaluate to |Γ_𝒥| = rank − 1 (e.g. 3m²−9m+6 = 6 at m=3 while the cubic surface has rank L = 7). Verified against the LaTeX source. Not a finding against the paper.

7. **Minor, Lemma 2.4(ii).** "±(unit)" — the sign is absorbed in the unit; cosmetic.

I looked specifically for, and did not find: a position mismatch in Lemma 5.5 when ℓ = h or ℓ = 0; a missing case in the layout of Proposition 5.6 (removal(μ) against addition(μ̃) is impossible because ℓ+ℓ̃ ≤ 2h = L); a failure of the exact coverage j = q−1−F in Proposition 5.8 (both hand-derived from (5.1) in all three cases and machine-tested with a sensitive negative control); an option outside Par_m in §5.4; a use of Theorem A anywhere in §2–§5 (none; all cross-references checked); a wrong direction in Proposition 2.5 (≤ follows from Prop 2.1's ≥ on the quotient); a dependence of §5 on the characteristic beyond the field of coefficients (none: Lemma 5.7 holds over Z).

## WHAT I DID NOT CHECK
- **The proofs inside [DS]** of Theorem 1.1(a) (which rests on Pham's theorem and the intersection computation of [DS, §3]), of Claim 4.3 beyond reading its two-line argument, and of Corollary 1.5 / Theorem 1.4. I verified the *statements* symbol by symbol against the arXiv v3 LaTeX source, not their proofs. If [DS, Theorem 1.1(a)] were wrong, the Main Theorem would not follow; this is the one external dependency.
- **Other references**: [De14], [De15, Conjecture 4.4], [CM], [Jam], [Jan], [Mat], [DCP], [GP], [Ta], [CLO] were not opened. They enter only remarks and Appendix A's Remark 3 (Tanisaki), not the proofs of the Main Theorem or Theorem A (Macaulay's basis theorem [CLO] is standard).
- **The paper's own verification record (§8)** and its repository: not opened, not reproduced. All computations reported above are my own, written from the paper's definitions.
- **Large cells**: (3,9) = 190 120, (6,3) = 3 432, (5,3) = 924, (1,81), (2,27) were not recomputed (my dense engine handles up to (2,9) in ~10 s). None is needed by the proof.
- **Proposition 2.6, x-form**: hand-check of the y-form only; the substitution to x_0..x_{2k+1} was only confirmed numerically at (1,3), (2,3), (1,9). Used only in §7, not in the Main Theorem.
- **Proposition 7.1 (sandwich)**: proof read and found plausible; confirmed numerically at three cells. Not used in the Main Theorem.
- **Theorem A.12 (row inclusions)**: re-derived by hand in all four cases (lower, value-0, new-class, raise) but **not machine-tested at the level of individual row inclusions**; machine checks of Appendix A were: the final count dim F_p[x]/(e_odd; x^q) = N_q(n) at 75 cells (p ∈ {3,5,7}, q ≤ 9, n ≤ 4) plus the char-2 failures, and exact identity checks of Lemmas A.8 (P)(B)(A)(V), A.9 and A.10 at random instances (q = 3, 5).
- **Remarks explicitly not claimed by the paper** (Remark 4.2(3) Specht route, Remark 5.9 equality/leading monomials, Remark 5.10 p ≥ 5): not examined.
- **§9 (method note) and the historical claims of §1.4**: not verifiable from the paper and not relevant to correctness.
- **Files**: all scripts and logs are in `checks/` next to this report (`p2test.py`, `ideal.py`, `sform.py`, `downset.py`, `p3test.py`, `thmA.py`, `fact72.py`, `thm41.py`, `prop26.py`, `lemA2.py`, and the `.log` files).

## 5 · HOW TO MAKE THE PAPER MORE ROBUST AND BRILLIANT

Written as the referee of a top journal who has just spent a day trying to break the paper and failed. What I would still ask for before accepting, in order of importance.

### 5.1 What I would demand

1. **A self-contained one-page statement of the algebraic theorem, before any topology.** The paper's real content is Theorem 5.3 plus the translation. A reader should meet, on page 2, the following box: *"Let F be any field, q odd, C = F[y_1..y_{2k+1}]/(y_i^{q−1}), D(a,b) = (b^{q−1}−a^{q−1})/(a+b). Then dim_F (D_J : J a perfect matching of {0..2k+1}) C = (2k+2)!·[x^{2k+2}] I_0(2x)^{(q−1)/2}."* This is characteristic-free (see §6 below: nothing in §5 uses 3) and is more striking than the topological corollary. State it as **Theorem B** and let the Main Theorem be its corollary via [DS].

2. **State [DS] inputs as one black box, once.** Collect Theorem 1.1(a), Claim 4.3, Corollary 1.5 (and Theorem 1.4, which the rank clause uses — Finding 1) into a single "Theorem 0 ([DS])" with the exact statement the paper needs: *"H_n/L_K is torsion free iff dim_{F_p}(R/(ψ_J : J ∈ K) ⊗ F_p) = m^{n+1} − |Γ_K| for every prime p | m."* Then Proposition 2.1 becomes two lines and the referee sees at a glance exactly what is imported.

3. **A worked example of the whole induction at (k, q) = (1, 3) and (1, 9).** At (1,3): m = 3, Λ = {(1)}, three generators y_2−y_1 (×signs), peel y_1: F values of μ = ∅ and μ = (2), the layers Λ_0 = {∅,(2)}, Λ_1 = {∅}, and the slices W_0, W_1 with the certificates of Proposition 5.8 written out. Half a page; it makes P1–P3 concrete and lets a reader verify the mechanism without reading the general proof. The (1,9) example shows the three kinds of options (removal, new class, addition) that (1,3) does not.

4. **One figure.** The chain of Lemma 5.5 drawn as a Young diagram with the q−1 options in order (remove from row ℓ … remove from row 1 | new box in row ℓ+1 (repeated q−1−2ℓ times) | add to row ℓ … add to row 1), and next to it the slice index j = q−1−F. This single picture *is* the proof of Proposition 5.8 and (5.1); it would have saved me an hour.

5. **A table of the 7 cases of Proposition 5.6** (rows: case; columns: position range, option of μ, option of μ̃, the inequality needed, where it can fail, the contradiction obtained). The prose proof is correct but a referee wants to see coverage at a glance. Add the one-line argument that removal(μ) vs addition(μ̃) cannot occur (ℓ+ℓ̃ ≤ 2h = L) *inside* the table.

6. **Make the "no slack" claim a Lemma, or drop the sentence.** "The coverage is exact … replacing q−1−F by q−2−F makes the statement false (§8)" is a computational remark inside a proof section. Either prove it (easy: at (k,q)=(1,3) the generator 1 of Λ_1 = {∅} does not lie in W_0 — one line) or move it to §8.

7. **Independence from Theorem A must be stated in the theorem environment, not in remarks.** Put "The proof of the Main Theorem uses only §2 and §5" directly under the Main Theorem. Currently it is said in §1.3, §6, §10 — three remarks; one sentence in the right place is stronger.

8. **Compress the sociology.** §1.4 (history), §8 (verification record), §9 (method note) and §10 (seal) are together longer than §5. For a journal: keep §8 as a short "Computational corroboration" table (the Route 4 table, and one paragraph on the down-set tests), and move §1.4, §9, §10 and the list of dead routes to a supplementary document / the repository. A referee reads the proof; the campaign narrative makes the paper look less sure of itself, not more.

9. **§4 should be shortened to a remark or moved to an appendix.** It is a nice explicit basis, but §5 already covers q = 3 verbatim, and the ballot-path proof is a second, independent argument that the referee must also check. Either (a) keep it as Appendix B "An explicit basis for q = 3" or (b) keep only Theorem 4.1's statement and the Specht remark as a Remark after Corollary 5.4.

10. **Proposition 2.6 and §7 to an appendix.** They are not used in the proof. §7's message (the full family is necessary; the Sofá/Hamaca identification was wrong) is important and honest, but it belongs after the proof, as Appendix B "Why subfamilies fail", with Fact 7.2 and the 800/32767 count.

11. **Give Theorem A its own short paper, or its own appendix with a two-line pointer.** The two results share nothing but the peeling idea. The current paper spends abstract space and §1.3, §6, §7 explaining what Theorem A is *not*. A referee for the Main Theorem should not have to referee 8 pages of Θ^s_L(A;B) identities. If it stays: put the "dictionary" (Definition A.2) and the row inclusions (Theorem A.12) in a table like the one suggested in item 5.

### 5.2 Expand / shorten

- **Expand:** Lemma 2.3(i) — say explicitly "F_3[t]/(t^q−1) is local with maximal ideal (t−1) = (y) and y^{q−1} ≠ 0" before concluding; Lemma 5.1(iv) — one sentence that F(M') is the fibre of Z over M'; Proposition 5.8 — the phrase "exactly one of (α),(β),(γ) occurs" deserves its one-line justification (chain + F ≥ 1).
- **Shorten:** Lemma 2.2's proof (the bijection and the exponential formula are standard; two sentences); §3's table (keep k ≤ 3, the rest is in the repository); Remarks 4.2, 5.9, 5.10 (merge into one "Remarks" paragraph); §8 (see item 8).

### 5.3 What is missing

- A **glossary of notation** (T, h, Par_m, ≼, S_t, r̄_j, r̲_j, opt_p, F_Λ, Λ_i, W_j, V_Λ, Z_Λ, tight pattern). I kept my own; the paper should provide it.
- The **characteristic-free statement** of Theorem 5.3 (over any field, or over Z: the tight-pattern products have integer coefficients and the argument produces integer certificates, so dim ≥ |Z_Λ| holds over every field). This costs nothing and turns Remark 5.10 into a theorem (see §6).
- A **remark on what fails for subfamilies inside the proof**: say in Lemma 5.2 that for K ⊊ 𝒥 the ideal V_{(1)} is replaced by a smaller one that is not of the form V_Λ, so P3 has no analogue; the reader then sees exactly where the full family enters, instead of being told in Remark 5.9(3).
- **Reference to the published version of [DS]** for the numbering (the arXiv v3 numbering agrees with what the paper cites; state that you checked both).

### 5.4 The one-page version of the main idea

If I had to explain the proof on one page: *"The ideal is a sum of monomial-like pieces indexed by matchings. Peel one variable. Each coefficient slice of the ideal is again an ideal of the same type, indexed by a down-set of partitions under weak dominance; each layer of the point set is the fibre count of that down-set. Both sides are additive in the slices/layers, so it suffices to show every layer's ideal sits in the matching slice. The only algebra needed is that a Vandermonde with one row replaced by y^t vanishes for t small and equals the Vandermonde at t = r−1 — which converts the divided difference D(y_1,y_b) into a slice certificate. The combinatorics is that the q−1 values of the new coordinate form a chain, and chains dominate chains position by position."* Put this paragraph at the start of §5, with the figure of item 4.

### 5.5 What would make a referee trust it faster

- The four independent machine tests I would want to see reproducible in < 1 minute each, with a one-line command: P2 on all comparable pairs; (S) at (2,9); down-sets at (9,4); Proposition 5.8 slice by slice at (9,3) with the negative control. My versions are in `checks/`; the paper should ship equivalents in a single script with expected outputs.
- A statement of which lemmas are *identities over Z* (5.7, 2.4(i), D's definition) versus *inequalities of partitions* (5.5, 5.6) versus *linear algebra* (5.1, 5.8). Trust rises when the reader sees that no step mixes the three.

## 6 · OPINION: HOW TO PROVE THE CASE p ≥ 5

Short answer: **the paper already proves it.** Having re-derived §2 against [DS] and §5 by hand, I find no step that uses the prime 3 as such. The only arithmetic inputs are: (i) the field has characteristic p and q = p^v (Frobenius); (ii) 2 is invertible; (iii) q is odd. Replacing F_3 by F_p throughout, with p odd, gives the Main Theorem for every m = p^v with p an odd prime. Remark 5.10's caution is more than the mathematics requires. Details, then the harder cases (m = 2^v, composite m), then the computations I ran (predictions stated before each run).

### 6.1 §2, step by step: what uses 3, what uses only "p odd, q = p^v"

| Step | What it needs | Uses 3? |
|---|---|---|
| Prop 2.1 | [DS] Thm 1.1(a), Claim 4.3 (p=0), Cor 1.5; right exactness of ⊗ | no (any m, any p \| m) |
| Lemma 2.2 / 3.1 (counts) | q odd (inversion/negation fixed-point free on μ_q∖{1}, on F_q^×) | no |
| Lemma 2.3(i) | t^q−1 = (t−1)^q (char p, q = p^v); t+1 = 2+(t−1) a unit (**2 ≠ 0**) | no |
| Lemma 2.3(ii) | t_j+t_k = 2+(t_j−1)+(t_k−1) a unit (**2 ≠ 0**) | no |
| Lemma 2.3(iii) | (u−1)φ(u) = u^q−1 = (u−1)^q (char p, q = p^v), domain | no |
| D(a,b) = (b^{q−1}−a^{q−1})/(a+b) | q−2 odd; identity over Z | no |
| Lemma 2.4(i) | (a+b)^q = a^q+b^q (char p); q−1 even | no |
| Lemma 2.4(ii), Prop 2.5 | bookkeeping; kernel of Y· on the box ring | no |
| Prop 2.6 (not needed) | ℓ^q = Σ c_i y_i^q for c_i ∈ F_p (c^p = c) | no |

So §2 holds verbatim over F_p for every odd prime p and q = p^v. The literal statement "for m = q = 3^v only p = 3 matters" becomes "for m = q = p^v only p matters".

### 6.2 §5: where could a 3 hide?

Nowhere. Every polynomial identity (D's expansion, Lemma 5.7(i)–(iii), the Vandermonde factorisation, the certificate f in Prop 5.8(γ)) holds over Z with coefficients ±1, so the top coefficients are units in every field. P1, Chain, P2 are statements about partitions and about a finite set T with a fixed-point-free involution; they use only h = (q−1)/2 (q odd). Lemma 5.1 uses only y_1^{j+1} ≠ 0 for j+1 ≤ q−2. Lemma 5.7(iii) needs |B| ≤ q−2, and |B| ≤ h−1. Hence:

> **Theorem 5.3 is characteristic-free:** for every field F, every odd q and every ≼-down-set Λ ⊆ Par_m, dim_F V_Λ ≥ |Z_Λ| in F[y_1..y_m]/(y_i^{q−1}).

(Indeed the certificates are integer polynomials, so the statement holds over Z in the sense that the F-span has the stated dimension for every F.) The characteristic enters only when Theorem 5.3 is *matched* to the topology through §2, which requires m = q = p^v with the coefficient field F_p. Over F_5 with q = 3, for instance, Theorem 5.3 still gives dim ≥ Q_k(3), and the elementary bound ≤ of Prop 2.5 has no meaning, but that is irrelevant: the theorem the paper needs is the case F = F_p, q = p^v.

**Recommendation.** Rewrite §2 with a prime p in place of 3 (the table above is the list of places to touch), state Theorem 5.3 over an arbitrary field, and claim the Main Theorem for **all odd prime powers m**. This is one day of editing and no new mathematics; it also removes the odd-looking gap between "3^v" and "p^v" that every referee will ask about.

### 6.3 Computations (prediction first, then result; code `checks/pgeq5.py`, `checks/downset_p.py`)

| Test | Prediction | Result |
|---|---|---|
| y-form (Prop 2.5 count) over F_5, (k,q)=(1,5) | Q_1(5)=36 | 36 ✓ |
| over F_5, (2,5) | Q_2(5)=400 | 400 ✓ |
| over F_5, (1,25) | Q_1(25)=1656 | 1656 ✓ |
| over F_5, (3,5) (7 variables, box 4) | Q_3(5)=4900 | 4900 ✓ (23 s) |
| over F_7, (1,7) / (2,7) | 90 / 1860 | 90 / 1860 ✓ |
| **literal [DS] form** F_p[t]/(t_i^m−1)/(ψ_J), (k,m,p)=(1,5,5) | m^{2k+1}−\|Γ\| = 89 | 89 ✓ |
| (1,7,7) / (2,5,5) | 253 / 2725 | 253 / 2725 ✓ |
| Theorem 5.3, every down-set, coefficient field F_5, (q,m)=(5,3),(5,4) and F_7, (7,3) | dim V_Λ = \|Z_Λ\| | equality in all 16 down-sets ✓ |

The literal-form rows are, via [DS, Thm 1.1(a) + Claim 4.3], Conjecture 1.2 itself at (k, m) = (1,5), (1,7), (2,5), computed without any of the paper's machinery: they confirm both the conjecture at those cells (the (4, m ≤ 12) cells are also in [DS, §5]) and the translation over F_5, F_7. All predictions held.

### 6.4 Literature (what I could check, and what should still be checked)

- [DS] (2016) proves the criterion and confirms (n,m) = (4, 3..12), (6,3), (6,4), (6,5), (8,3) by computer. [De14] proves d = 1 for all m. The 2015 survey [De15] (arXiv:1512.06199, "a brief systematic overview") lists the higher-dimensional statement as open.
- arXiv searches (author Degtyarev + "Fermat"; "Fermat varieties" + torsion; "Fermat" + "projective subspaces") return nothing later that claims the higher-dimensional conjecture for any infinite family of m. So, as far as arXiv shows, **m = p^v with p ≥ 5 is not known**, and neither is any composite m beyond the computed cells.
- **Still to check by the authors:** MathSciNet/zbMATH citations of [DS] (I could not consult them); Shimada's work on Fermat varieties in positive characteristic (Proc. LMS 2001) uses a different lattice (algebraic cycles in char p) — related count, different statement; and the Aoki–Shioda / Schütt–Shioda–van Luijk line for surfaces, superseded by [De14].

### 6.5 m = 2^v (characteristic 2)

Here §2 breaks at Lemma 2.3: in characteristic 2, t+1 = t−1 is not a unit, y = t−t^{−1} = t^{−1}(t−1)^2 generates (t−1)^2, not (t−1), and the involution y ↦ −y is trivial. The count also changes: inversion on μ_m∖{1} has the fixed point −1, so |Γ_𝒥| = N!·[x^N] e^x I_0(2x)^{m/2−1} (this is [DS, Remark 4.4]'s δ_m term). Curiously, this is exactly Theorem A's N_{m−1}(N) — a sum-type count with an e^x factor — and Theorem A is precisely the statement that fails in characteristic 2 (Remark 6.3). So the even case is not a routine extension: it needs a new coordinate (y := t−1 gives t_jt_k−1 = y_j+y_k+y_jy_k, no longer a unit times a linear form) and probably a new combinatorial model with one "self-paired" class. Nothing in §5 transfers as is. My literal-form check at (k,m,p) = (1,4,2) gives 45 = 64−19 (predicted; k=1 is [De14]), so the [DS] machinery is fine there; the missing piece is entirely the algebra. I would leave m = 2^v to a separate paper.

### 6.6 m with two different primes: a concrete plan

Let m = p^a m′ with p odd, gcd(m′, p) = 1, m′ > 1. Over F̄_p, t^m − 1 = (t^{m′} − 1)^{p^a}, so F̄_p[t]/(t^m−1) = Π_{ζ ∈ μ_{m′}} F̄_p[t]/((t−ζ)^{p^a}) and F̄_p[G] = Π_{ζ ∈ μ_{m′}^{2k+1}} (local rings). Everything — the ideal (ψ̄_J) and the count |Γ_K| — localises at the components ζ. Writing t_i = ζ_i s_i, one checks:
- φ(t_jt_k) = (t_jt_k−ζ_jζ_k)^{p^a}·(unit)/(t_jt_k−1) vanishes identically on the component if ζ_jζ_k ≠ 1 (because s^{p^a} = 1 there), and equals (s_js_k−1)^{p^a−1}·(unit) if ζ_jζ_k = 1;
- t_{k_i}−1 is a unit if ζ_{k_i} ≠ 1 and equals s_{k_i}−1 if ζ_{k_i} = 1.
So on the component ζ only the matchings J that pair each index of "colour" c = ζ_i with an index of colour c^{−1} survive, and the local generator is a **product over colour blocks** of independent variables. Since the ideal generated by products of block generators is the tensor product of the block ideals, and the local point count multiplies likewise, **the conjecture at (k, m) reduces to three block statements at the box p^a =: q, each in the y-coordinates of §2:**
- **(b) colour 1** (indices with ζ_i = 1): exactly the paper's ideal (D_P : P) at box q−1 — Theorem 5.3 at the root (1) if the block has odd size (0 ∈ block), at Λ = {∅} if even. **Done by the paper.**
- **(c) colour −1** (only if m′ is even): generators Π_{(j,k)∈P}(y_j+y_k)^{q−1} over perfect matchings of the block, in F_p[y]/(y_i^q) — "Y-free". Required dimension: N_q(2r) = (2r)!·[x^{2r}] e^x I_0(2x)^{(q−1)/2} (points of μ_q^{2r} closed under inversion, 1 now allowed). By the annihilator duality of Prop 2.6 this is the statement ∩_P (I_P + (x_i^q)) = E + (x_i^q), whose "≤" half is **Theorem A** (Corollary 6.1) and whose "≥" half is a Y-free analogue of Theorem 5.3 at the odd box. So Theorem A, which the paper keeps carefully separate from the Main Theorem, is exactly half of what the composite case needs; this is the honest role of A = P.
- **(a) colour pair {c, c^{−1}}, c² ≠ 1**, r indices of each colour: generators Π_j (y_j + y′_{σ(j)})^{q−1} over bijections σ, in the box q; required dimension (r!)²·[x^{2r}] I_0(2x)^q.
- The pair {0, k_0} sits in the block of colour ζ_0^{−1}; when that colour is not 1 the factor t_{k_0}−1 is a unit, so the block statement is the Y-free one with one distinguished index.

**Plan.** (1) Write the localisation lemma above (one page; all the identities are in Lemma 2.3 with ζ-shifts). (2) Prove the Y-free Theorem 5.3: same peeling, same partitions, but the point set now allows the value 0 ∈ F_q, i.e. one extra "self-paired" class of size 1 — so Par_m must carry one extra row type and the chain of Lemma 5.5 gets one extra option (the value 0), with the corresponding extra construction in Prop 5.8. The e^x factor in the count is the signature of that extra class. (3) The bipartite block (a) is the same with two colours and no self-pairing; its chain is the same chain with the removal/addition options split by colour. (4) Assemble. Each of (2), (3) is a paper of the size of §5; the payoff is the conjecture for **all odd m**, and, with (6.5), for all m.

Small computations (prediction stated first; `checks/yfree.py`):

| Block | (r, q, p) | Predicted | Result |
|---|---|---|---|
| (c) Y-free symmetric | (1,3,3) / (2,3,3) / (3,3,3) | 3 / 19 / 141 | 3 / 19 / 141 ✓ |
| (c) | (1,5,5) / (2,5,5) | 5 / 61 | 5 / 61 ✓ |
| (c) | (2,9,3) | 217 | 217 ✓ |
| (c), **wrong characteristic** control | (2,3, p=5) | 19 | **30 ≠ 19** |
| (a) Y-free bipartite | (1,3,3) / (2,3,3) / (3,3,3) | 3 / 15 / 93 | 3 / 15 / 93 ✓ |
| (a) | (1,5,5) / (2,5,5) | 5 / 45 | 5 / 45 ✓ |
| literal [DS] form, composite m: (k,m,p) = (1,6,2),(1,6,3),(1,10,2),(1,10,5),(1,15,3),(1,15,5) | m³−\|Γ\| = 155,155,783,783,2829,2829 | all ✓ |
| literal form (2,6,2) and (2,6,3) (7776-dim group ring) | 6⁵−1001 = 6775 | 6775, 6775 ✓ |

All block predictions held in the right characteristic, which supports the reduction of §6.6; the wrong-characteristic control shows that, unlike Theorem 5.3, **the Y-free blocks are not characteristic-free** (the binomial coefficients of (y_j+y_k)^{q−1} matter), so their proof must use p | q — this is where a Y-free §5 would differ from the present one. The composite literal-form cells at k = 1 are [De14]; the (2,6) cells are in [DS, §5]; I include them because they were produced by my own code from the definitions, and because they confirm the count 6⁵ − 1001 with the δ_m term.

### 6.7 Summary of the opinion

1. **p ≥ 5, m = p^v:** already proved by the paper's argument; change "3" to "p" in §2, state Theorem 5.3 over any field, claim it. I ran the translation and the count at (1,5), (2,5), (3,5), (1,25), (1,7), (2,7): all as predicted.
2. **m = 2^v:** genuinely open; Lemma 2.3 and the count both change; Theorem A's failure in characteristic 2 is a warning that the sum-type model is the wrong one there.
3. **Composite m (odd):** reduces by localisation to Theorem 5.3 (done) plus two Y-free block theorems at the odd box, one of which has Theorem A as its upper half. That is the natural sequel, and it is where the campaign's A = P work finally becomes relevant.
