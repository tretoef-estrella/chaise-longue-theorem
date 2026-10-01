# COLD REPORT — PAPER_OFICIAL_v10 (new material) and THE_REGULAR_CENTRALIZER_NOTE_v1

Cold reader: independent referee, working alone. Date: 2026-10-01. Language: English.
Files read: `VIVOS/MISIONES_TRAS_BARRIDO/PAPER_OFICIAL_v10.md` (1288 lines; the new parts and their context),
`VIVOS/MISIONES_TRAS_BARRIDO/THE_REGULAR_CENTRALIZER_NOTE_v1.md` (213 lines; all of it),
and the sources in `FUENTES_ORIGINALES_TEOREMA_A_2026-10-01/` (`brr.txt` §2.1–§2.6 in full, `brr_2005.05583.tex`,
`ginzburg_9803141.tex` §4, `riche_1411.3112.tex` introduction + a search of the whole source, `liu.txt` introduction).
Own code and logs: `cold_*.py`, `cold_*.log` in this folder. Line numbers below are those of the `.md` files.

## 0. Verdict

**HOLDS.** No claimed result is false. Findings: **FATAL 0 · GAP 1 · ERROR 3 · PRESENTATION 13.**

The new mathematics (Proposition 8.5, Corollary 8.6(i), Corollary 8.6(ii) modulo [BRR], the dictionary of Remark 8.4(1),
the derivation of Theorem A from [BRR, Proposition 2.12] in odd characteristic, the even-`q`/even-`n` statement of Remark 8.4(6),
Theorem 7.1 of the note) was re-derived by hand and confirmed by my own code. [BRR, Proposition 2.12] is quoted exactly, with its
exact standing hypotheses, and those hypotheses hold for `Spin_{2m+1}` (all `m ≥ 1`, every odd `ℓ`, no relation between `ℓ` and `q`)
and for `Sp_{2m}`. The attribution of the count of Theorem A to Kostant and to [BRR] is correct and I found no leftover sentence
that still claims the count as new.

The one GAP is a true statement with an argument that does not cover characteristic 2 (Remark 8.7(3); one line repairs it).
The three ERRORs are a false sentence inside a sketch that is labelled as a sketch (the determinant parity argument), a hypothesis
misquoted from [Gin], and an imprecise identification in the note. One PRESENTATION item is an **under-claim**: the equality
`dim F[L]/K_μ(L) = N_μ(n)` is in fact proved for every `μ` by the argument the note itself uses in Theorem 7.1.

---

## Findings (graded)

### GAP

**G1. Paper, Remark 8.7(3), line 748; note §5, line 123; (problem 7 of §13 relies on it).**
Sentence: «The inequality `≤` holds over every field, by the argument of Proposition 9.1».
Why: the argument of Proposition 9.1 needs a set `C` of `q` values with `0 ∈ C = −C` on which `v ↦ −v` has the single fixed point `0`.
In characteristic 2 there is no such set (`−v = v`). With any set of `q` values the point set of the union is
«every value occurs an even number of times», of cardinality `N!·[y^N] cosh(y)^q`, which is larger than `N_q(N)`:
`21` against `19` at `(q, N) = (3, 4)`, `183` against `141` at `(3, 6)` (computed, `cold_T1.log` and a direct count).
So in characteristic 2 that argument proves only `≤ 21`, not `≤ 19`. The statement itself is true.
Proposed text: «The inequality `≤` holds over every field. In characteristic `≠ 2` it is Proposition 8.5(iii) together with Theorem A
(or the argument of Proposition 9.1 with a set `C = −C` of `q` values). In characteristic `2` the argument of Proposition 9.1 does not apply;
but `Σ_J D_{q,J}C_q` is spanned by vectors with integer coordinates, so its dimension over any field is at most its dimension over `Q`.»

### ERROR

**E1. Paper, Remark 8.7(2), line 746; note §4.3, line 110 (inside a sketch, labelled as a sketch, used by nothing).**
Sentence: «for odd `r` the group is `SO_r`; an invariant involving the determinant would leave an odd number `N + 2d − r` of factors to be paired, so none occurs».
Why: the parity count excludes an invariant with ONE determinant factor, not with two. For `N + 2d ≥ 2r` there are `SO_r`-invariants built from an even
number of determinants (for `r = 3`, `det(v_1,v_2,v_3)·det(v_4,v_5,v_6)` in `V^{⊗6}`); `N + 2d − 2r` is even. They are combinations of contractions
(`det·det` is the determinant of the Gram matrix), so the conclusion is right, but the sentence as written is false.
Proposed text: «for odd `r`, `O_r = {±1} × SO_r` and `−1` acts trivially on a tensor power of even degree `N + 2d`; so the invariants of `SO_r` there
are those of `O_r`, which are spanned by the complete contractions».
I found no other mistake in the sketch: the evaluation of a contraction at `e` is correct (a chain through `j` copies of `e` gives `±x_a^j D_r(x_a,x_b)`,
a closed chain gives `tr(e^j) = 0`), and every `x^β·D_{r,J}` is obtained.

**E2. Paper, Remark 8.4(2), line 717; note §2.1, line 60 (quotation of the source).**
Sentence: «Let `G` be a connected reductive group over `C` … we quote the statement from [Gin, Proposition 4.2]».
Why: [Gin, §4] reads «Given a complex connected **semisimple** group `G`» (source lines 649 and 669–675); Proposition 4.2 is stated in that setting.
Harmless for `SO_{2m+1}` and `Sp_{2m}`, but it is not the quoted hypothesis.
Proposed text: «Let `G` be a connected semisimple group over `C` …».
(The numbering «Proposition 4.2» is right: [Gin] numbers theorems with the equation counter, reset in §4; Theorem 4.1, Proposition 4.2.)

**E3. Note, Summary item 3, line 17, and the table of §8, line 172.**
Sentences: «Theorem B of [CL], which is the algebraic form of Conjecture 1.2 of Degtyarev and Shimada»; table row
«**Theorem B / Conjecture 1.2 of [DS] for odd degree** | this project | proved; Lean-checked in its algebraic form».
Why: Theorem B is the algebraic form of the conjecture only for degree `m = p^v` ([CL, Proposition 2.5]); for the other odd degrees the algebraic form is
Main Theorem′ (Theorem B, Theorem C and the colour reduction). And [CL, §14] gives the conjecture as «PROVED, modulo Pham's theorem and [DS, Theorem 2.2]»,
not as «proved». A table whose purpose is «whose is what» should not be looser than the paper. (§4.2 of the note, line 106, says it correctly.)
Proposed text, item 3: «Theorem B of [CL], which for degree `m = p^v` is the algebraic form of Conjecture 1.2 …».
Proposed row: «Theorem B (every field, every odd `q`); Conjecture 1.2 of [DS] for every odd degree | this project ([CL]) | Theorem B and Main Theorem′ proved and Lean-checked; the conjecture proved modulo Pham's theorem and [DS, Theorem 2.2]».

### PRESENTATION

**P1. UNDER-CLAIM. Paper, Remark 8.4(4), line 721; §12.5, line 893; note §2.3(c), line 72, and §8 table.**
Sentence: «equality is proved for `μ = ∅` and computed at `178` cells».
Why: equality is proved for EVERY `μ` with `ℓ(μ) ≤ h` and every `n`, by the argument the note uses in the proof of Theorem 7.1.
Let `P(μ)`: «`dim F[L]/K_μ(L) = N_μ(n)` for every `n`». `P(∅)` is Theorem A. If `P(μ)`, then at `n + 1` variables the chain of Theorem A.15,
`N_μ(n+1) = Σ_a dim F[L]/R_a ≤ Σ_a dim F[L]/K_{child_a(μ)}(L) ≤ Σ_a N_{child_a(μ)}(n) = N_μ(n+1)`, is a chain of equalities, so `P(child_a(μ))` holds
and `R_a(K_μ(L∪z)) = K_{child_a(μ)}(L)`. Every `μ` with `ℓ(μ) ≤ h` is reached from `∅` (new-class steps to `(1^ℓ)`, then raises).
I checked `μ = (1)` with my own code at 11 cells (`cold_T5.log`).
Proposed text: add «Corollary A.17. For every `μ` with `ℓ(μ) ≤ h` and every `n`, `dim F[L]/K_μ(L) = N_μ(n)`, and
`R_a(K_μ(L∪z)) = K_{child_a(μ)}(L)` for every `a`»; in Remark 8.4(4) write «with equality (Corollary A.17)»; keep the 178 cells as a check.
Consequence for the note: the «explicit order of the steps» of §7 (line 154) is the order of Definition A.2 of [CL], so it is proved too, not only
«equal to the definition in 3 605 profiles».

**P2. Paper §12.6, line 907.** «PLACEHOLDER: Remark 8.4, Proposition 8.5, Corollary 8.6 and Remark 8.7 have not yet been read cold.» The word PLACEHOLDER must not be published; replace by the record of this reading.

**P3. Paper §1.8, line 107.** Three versions are called the present one: «The present version (v8) adds …», «Version 9 (the present one) corrects …», «Version 10 (the present one) corrects …». Proposed: «Version 8 added …», «Version 9 corrected …», «Version 10 (the present one) corrects …».

**P4. «Infinite field» dropped.** Abstract (line 19: «the ring is the space of coinvariants of the centralizer of a regular unipotent element»), Remark 8.7(1) (line 744, the sentence in bold: «that space is the whole space of invariants of the centralizer»), note Summary item 1, note §4.1 line 94 and «In words» line 104.
Why: this is true for the centralizer as an algebraic group, or over an infinite field (Remark 8.4(1) says «for `F` infinite», correctly). For the group of `F`-points over a finite field it is false: over `F_3` the coinvariants of `Z(F_3)` have dimension `9`, `27`, `19` at `(q, n) = (3,3), (3,4), (5,3)`, against `7`, `19`, `13` for the ring of Theorem A (`cold_T3.log`, part (c)).
Proposed: add «(as an algebraic group; equivalently, over an infinite field)» at the first occurrence in each place.

**P5. Corollary 8.6(ii), line 740; §14, line 947; §9.1, line 765.** The statement says «Modulo [BRR, Proposition 2.12]: if `char F ≠ 2`», the proof says «(on [Kos] in characteristic `0`)», §14 says «modulo [BRR, Proposition 2.12]» only.
Either add «and [Kos] in characteristic `0`» to the statement and to §14, or, better, remove the dependence on [Kos] (which was not read in the original): for the ring `M_Z = Z[x]/((e_j : j odd) + (x_i^r))`, `dim_Q ≤ dim_{F_p}` for every `p`, so [BRR] at one odd prime gives `dim_Q ≤ Q_k(q)`, and Proposition 8.5(iii) with Corollary 8.6(i) over `Q` gives `≥`. The same remark applies to Theorem A in characteristic `0` ([BRR] at one odd prime and Proposition A.5) and to Remark 8.4(6).

**P6. Remark 8.7(3), line 748.** (a) «that is, `⋂_J (I_J + (x_i^q)) = (e_j : j odd) + (x_i^q)` by Theorem A» needs «for `char F ≠ 2`»: in characteristic 2 the two ideals differ (colengths `19` and `21` at `(3,4)`, `141` and `183` at `(3,6)`, `1001` and `1205` at `(5,6)`), although the dimension statement holds there in the cells computed. (b) «by (2) there is equality in characteristic `0`» should read «by the sketch (2)», as problem 7 of §13 does.

**P7. Remark 8.7(1), line 744.** «By Proposition 2.5, for `m = p^v` Conjecture 1.2 of [DS] is equivalent to this statement over `F_p` for `Sp_{m−1}`.» It is equivalent to the first clause (the dimension is `Q_k(m)`), through Theorem 0 and for `k ≥ 1`. Proposed: «… is equivalent to the first half of this statement (the dimension count) over `F_p` for `Sp_{m−1}` (for `k ≥ 1`, through Theorem 0)».

**P8. Clashes of symbols inside §8.** `m = (q−1)/2` in Remark 8.4 (line 705) and `m =` the degree in Remark 8.7(1) («for `m = p^v` … `Sp_{m−1}`») and in the table of §1.9, which does not list the use of §8; `Z` is the centralizer, and also the integers (`Z^m`, `Z[x_1,…]`, «closed walks on `Z^m`» two lines after «`(V^{⊗n})^Z`»); `M` is the abelian group of Corollary 8.2 and the space of Corollary 8.6; `h := 1 + f` in Remark 8.4(1) against `h = (q−1)/2`; `G` is the isometry group and the group of [DS]. Proposed: write `𝒵` (or `Z_e`) for the centralizer, `s` or `ρ` for the rank in Remark 8.4, `𝓜` for the space of Corollary 8.6, and add §8 to the row of `m` in §1.9.

**P9. Remark 8.4(1), line 707.** «its determinant is `f(0)^q = f(0)`»: the second equality uses `f(0) = ±1`, which follows from `f(e)f(−e) = 1`; say so («the constant term gives `f(0) = ±1`, so `det f(e) = f(0)^q = f(0)`»). Line 719: «The only bad prime of type `B_m` is `2`»: for `m = 1` the type is `A_1` and there is no bad prime; write «`ℓ` odd is good for `G`».

**P10. Remark 8.7(2), line 746.** Kostant's surjectivity gives the invariants of the group centralizer `G^e`, not of `𝔤^e`. They coincide here (for `SO_r`, `G^e` is connected; for `Sp_r`, `G^e = {±1} × (unipotent)` and `−1` acts trivially because `N` is even). One clause is enough. The note (§4.3) writes `W^{G^e}`; the two texts should agree.

**P11. References.** (a) [Kos] is annotated «Remarks 8.4 and 8.7 only» but is cited in §1.6, in the proof of Corollary 8.6, in §13 (problem 6) and §14; [BRR] is annotated «Remark 8.4, Corollary 8.6» but is cited in §1.6, §1.8, §9.1, §13 and §14. (b) The title page of the cited version of [BRR] (v2, 4 July 2024; first page of `brr.txt`) reads «Modular affine Hecke category and regular unipotent centralizer», without «, I»; check the title against the arXiv listing. (c) [Ric]: the reference says «the introduction and §2.2 were read», §12.6 says «the introduction of [Ric]»; the entry has no version or date; it is placed between [Shi79] and [SK]. (d) The sentence of Remark 8.4(3) «[Ric] … does not contain the count» is about a paper of which only the introduction and §2.2 were read; I searched the whole source for the count and did not find it, so the sentence is safe, but say «we did not find the count in it».

**P12. Note, Theorem 7.1 and its proof, lines 148–152.** (a) The definition of `r_j(w)` is ambiguous when two steps have the same number `N_{j−1}(p_j − c)`; say «with any fixed rule for ties; the generating function does not depend on the rule» (I confirmed this with two rules). (b) The proof uses, without saying it, that `N_μ(n)` is the number of walks of length `n` from `0` to the point `Σμ_iε_i` and that the `q` children of Definition A.2 are the shapes of the `q` points `p − c` (this is Lemma A.3 of [CL]); add one sentence. (c) «the numbers `N_{child_a(μ)}(n)` decrease with `a`»: «do not increase». (d) «The same argument then applies to each child»: say that it is applied for every `n` (see P1).

**P13. Note, small inconsistencies with the paper.** (a) §3, line 84: «In `8` cells (`q ∈ {2,4,6,8}`) the dimension … is the number of walks from `0` to `ε_1`»: by Remark 8.4(6) of the paper the `8` cells are of both parities of `n`; the sentence holds for the cells with odd `n`. (b) §5, line 128: «the project took it [the bone] to be equivalent to Conjecture 1.2»; the paper (§1.8) says the project took the count `A_k(q) = P_k(q)` of Theorem A to be the algebraic form. Use one account. (c) §4.1, line 94: «The right-hand side of (iii) is `(V^{⊗N})^Z`» needs `char F ≠ 2` and `F` infinite, while Proposition 4.1 is stated «over every field»; and no duality is needed (the invariants of `Z` are by definition the annihilator of the ideal generated by the elements `Π f(x) − 1`). (d) «In words», line 104: add «modulo [BRR, Proposition 2.12]» to «This holds over every field of characteristic `≠ 2`».

---

## A. Remark 8.4(1), the dictionary — HOLDS

Re-derived by hand, sentence by sentence:
- the form is nondegenerate and symmetric (`(−1)^b = (−1)^{2m−a} = (−1)^a`); `⟨eu, v⟩ = −⟨u, ev⟩` on basis vectors, including the boundary `a = q − 1`;
- the commutant of `e` is `F[e]` (`V` is cyclic); the adjoint of `f(e)` is `f(−e)`, so `f(e)` is an isometry iff `f(e)f(−e) = 1`; then `f(0) = ±1` and `det f(e) = f(0)^q = f(0)` (see P9);
- `g_t`: `g_t(x)g_t(−x) = 1`, `g_t − 1 = 2te(1 − te)^{−1}` has rank `q − 1` for `t ≠ 0` (uses `2 ≠ 0`), and `te = (g_t − 1)(g_t + 1)^{−1}`, so the centralizer of `g_t` in `GL(V)` is `F[e]` and in `SO(V)` it is `Z`; in characteristic `≠ 2` a unipotent element of `SO_{2m+1}` with one Jordan block is regular;
- `E(t) − E(−t) = 2Σ_{j odd} e_j t^j`; `E(−t)^{−1}` is a polynomial in `t` over the box ring; the coefficient of `t^i` of `E(t)/E(−t) − 1` is `2e_i` plus a combination of the `e_j`, `j < i` odd (`i` odd), so the coefficients generate `(e_j : j odd)`; for infinite `F` the values at `t ∈ F` span the span of the coefficients;
- `h = 1 + f`: `h(−x)f(x) = f(x) + f(x)f(−x) = h(x)`; `H^−` is a unit (`H^−(0) = 2^n`); `H − H^− = 2·`(odd part of `H`); a homogeneous symmetric polynomial of odd degree is a polynomial in the `e_j` each of whose monomials contains an odd `e_j`;
- coinvariants and invariants: `V^{⊗n} ≅ (V^{⊗n})^*` as a `Z`-module through the invariant form, and `(M_Z)^* = (M^*)^Z`;
- characteristic `0`: `Lie Z` is the space of odd polynomials in `e` without constant term, basis `e, e^3, …, e^{2m−1}`; `e^j` acts as `p_j(L)`; Newton's identities give `(p_j : j odd) = (e_j : j odd)` when `Q ⊆ F`.

My code (`cold_T3_dictionary.py`, `cold_T3.log`; peak 32 MB, 3 s):
- the ideal generated by the `t`-coefficients of `E(t)/E(−t) − 1` equals `(e_j : j odd)` modulo the box at 10 cells `(r, n) = (3,3), (3,4), (3,5), (5,3), (5,4), (7,3), (4,3), (4,4), (2,5), (6,3)` in characteristics `3, 5, 7, 1000003` (40 of 40); in characteristic `2` the coefficients are all `0` (as they must be);
- for 6 random `f = (1 + a)/(1 − a)`, `a` odd, at 6 cells and 3 characteristics, `Π f(x_i) − 1 ∈ (e_odd)` (18 of 18);
- over `F_3` the `F_3`-points of `Z` do not generate `(e_odd)` (finding P4).

## B. Remark 8.4(3), [BRR, Proposition 2.12] and odd characteristic — HOLDS

Read in `brr.txt`: §2.1–§2.6 in full (lines 196–600), and the corresponding passage of the `.tex`.
- **Quotation.** [BRR, Proposition 2.12] reads: «For any finite-dimensional `G`-module `V` which admits a good filtration and any regular unipotent element `u ∈ G`, we have `dim(V^{Z_G(u)}) = dim(V^T)`.» The paper's quotation is exact (with `W` for `V`).
- **Standing hypotheses.** §2 fixes an algebraically closed field `K` of characteristic `ℓ`; §2.2: `G` connected reductive, `u ∈ G(K)` regular unipotent; §2.4 («From now on we assume»): (1) `G` has simply connected derived subgroup, (2) `ℓ` is good for `G`, (3) `X^*(T)/ZR` has no `ℓ`-torsion; §2.5: «We continue with the notation and assumptions of §2.4». There is no other hypothesis: nothing on `X_*(T)/ZR^∨` beyond (1) (which makes it free), nothing relating `ℓ` to the Coxeter number or to the module. The paper lists exactly these.
- **`Spin_{2m+1}`, `ℓ` odd.** Semisimple and simply connected; type `B_m` (`m ≥ 2`): the only bad prime is `2`; `m = 1`: `SL_2`, no bad prime; `X^*(T)/ZR ≅ Z/2`. So (1)–(3) hold for every odd `ℓ`, including `ℓ = 3 ≤ q` and `m = 1`.
- **`V` has a good filtration.** [BRR, proof of Lemma 2.13 and Figure 2.1]: for `B_n`, `n ≥ 2`, the Weyl module of highest weight `α_0 = ε_1` is simple iff `ℓ ≠ 2`, hence tilting, and it is the natural module of `SO_{2n+1}`. For `m = 1` it is the Weyl module `V(2)` of `SL_2`, simple for `ℓ ≥ 3`. Tensor products: [Jan, II.4.21] (the same citation [BRR] use in the proof of 2.12).
- **Scheme to group, `Spin` to `SO`.** [BRR, Proposition 2.2]: `Z_G(u)` is smooth when neither `X^*(T)/ZR` nor `X_*(T)/ZR^∨` has `ℓ`-torsion; so its invariants are those of `Z_G(u)(K)`. The kernel of `Spin → SO` is `{±1}`, central, trivial on `V`. If `g ∈ SO(V)(K)` commutes with `ū`, a lift satisfies `g̃ug̃^{−1} = zu` with `z ∈ {±1}`; `−u` has semisimple part `−1 ≠ 1`, so `z = 1`. Every regular unipotent element of `SO(V)` is the image of one of `Spin`, and they are all conjugate. Correct.
- **Conclusion.** Over `K`: `dim K[L]/I_q(L) = dim (V^{⊗n})_Z = dim (V^{⊗n})^Z = dim (V^{⊗n})^T = N_q(n)`; base change gives every field of odd characteristic. So Theorem A in odd characteristic does follow from [BRR, Proposition 2.12] and Remark 8.4(1), with no hidden hypothesis. Corollary 8.2 follows (Theorem A over `Q` and over `F_p`, `p` odd, as in A.8).
- Consistency test: where the hypothesis fails (`ℓ = 2`), Theorem A fails (my runs: `21, 65, 133` at `n = 4`, `q = 3, 5, 7`, as in Remark 8.3(1)).
- «the proof rests on the vanishing theorem and the good filtration of [KLT]»: correct ([BRR, Lemma 2.7] quotes [KLT, Theorem 2 and Theorem 7]; Corollary 2.10; proof of 2.12).
- [Ric]: the description is accurate (introduction read; the count does not appear in a search of the whole source). [Liu]: the description is accurate (Theorem 1 of the introduction).
- Remark 8.4(2): see E2. The deduction (regular nilpotent `e`, `𝔤^e = ⟨e, e^3, …⟩`, weights of `V` span the root lattice of `B_m`, zero weight space = closed walks) is correct.

## C. Remark 8.4(6), even `q`, `Sp_{2m}` — HOLDS

- For even `r` the form is alternating (`(−1)^b = −(−1)^a` when `a + b = r − 1`; `⟨x^a, x^a⟩ = 0`). The isometries commuting with `e` are the `f(e)` with `f(e)f(−e) = 1`, `f(0) = ±1`, all of determinant `1`: `{±1} × Z`. `−1` acts as `(−1)^n`.
- `Sp_{2m}` is simply connected, `ℓ ≠ 2` is good, `X^*(T)/ZR ≅ Z/2`, `V` is minuscule, so (1)–(3) of [BRR, §2.4] hold for odd `ℓ` and `V^{⊗n}` has a good filtration. For even `n`: `(V^{⊗n})^{Z_G(u)} = (V^{⊗n})^Z`, of dimension `dim (V^{⊗n})^T = n![y^n]I_0(2y)^m`. The dictionary of (1) holds verbatim (my code: the cells `(4,3), (4,4), (2,5), (6,3)` of part (a) above). In characteristic `0`: [Kos], weights in the root lattice of `C_m` iff `n` is even. Correct.
- Odd `n`: `W^T = 0`, and `W^{Z_G(u)} = 0` because `−1 ∈ Z_G(u)`; the proposition says nothing on `W^Z`. Correct; odd `n` is not covered.
- My code (`cold_T3.log`, part (d)): `dim F_p[x]/((e_odd) + (x_i^q))` at `(q, n) = (2,3), (2,4), (2,5), (4,3), (4,4), (4,5), (6,3)`: `3, 6, 10, 9, 36, 100, 15` in characteristics `3, 5, 7, 1000003` — the closed walks for even `n`, the walks `0 → ε_1` for odd `n` (28 of 28); in characteristic `2`: `4, 8, 16, 10, 40, 136, 16`, larger in all 7.

## D. Proposition 8.5 — HOLDS (every field, both parities of `r`)

Re-derived:
- (i) `(a + b)Σ_{u=0}^{r−1}(−1)^u a^u b^{r−1−u} = b^r + (−1)^{r−1}a^r` (terms `a^j b^{r−j}`, `1 ≤ j ≤ r − 1`, cancel). The quotient of `F[a,b]/(a^r, b^r)` by `(a + b)` is `F[b]/(b^r)`. `D_r·b^i` contains `(−1)^{r−1}a^{r−1}b^i ≠ 0` for `i ≤ r − 1`, degrees `r − 1 + i` distinct: the image of multiplication by `D_r` has dimension `≥ r`, the kernel contains `(a + b)` of dimension `r^2 − r`: equality. Tensor product: `ker(⊗f_i) = Σ_i (⋯ ⊗ ker f_i ⊗ ⋯)`. No hypothesis on the characteristic or on the parity of `r` is used.
- (ii) the pairing «coefficient of `Πx_i^{r−1}`» is perfect; `ann(I) = I^⊥`; `ann(ΣI_j) = ⋂ann(I_j)`; so `dim Σ_J D_{r,J}C_r = dim C_r − dim ⋂_J I_JC_r = dim F[x]/⋂_J(I_J + (x_i^r))`.
- (iii) `(1 + x_at)(1 + x_bt)D = (1 − x_b^2t^2)D`; the product over the pairs is even in `t`.

My code (`cold_T1_prop85_cor86.py`; `cold_T1.log`, `cold_T1b.log`, `cold_T1c.log`), with the intersection computed independently of the pairing, as the kernel of the stacked restriction maps `x_a ↦ −x_b`:

| `(r, N)` | `dim Σ_J D_{r,J}C_r` = `dim C_r/⋂_J I_J` (char 2, 3, 5, 1000003) | closed walks | `dim C_r/(e_odd)`, char 3, 5, 1000003 | char 2 |
|---|---|---|---|---|
| (2,2) | 2 | 2 | 2 | 2 |
| (2,4) | 6 | 6 | 6 | 8 |
| (2,6) | 20 | 20 | 20 | 32 |
| (2,8) | 70 | 70 | 70 | 128 |
| (4,2) | 4 | 4 | 4 | 4 |
| (4,4) | 36 | 36 | 36 | 40 |
| (4,6) | 400 | 400 | 400 | 544 |
| (6,4) | 90 | 90 | 90 | 96 |
| (3,2) | 3 | 3 | 3 | 3 |
| (3,4) | 19 | 19 | 19 | 21 |
| (3,6) | 141 | 141 | 141 | 183 |
| (5,2) | 5 | 5 | 5 | 5 |
| (5,4) | 61 | 61 | 61 | 65 |
| (7,4) | 127 | 127 | 127 | 133 |
| (5,6), char 2 and 3 only | 1001 | 1001 | 1001 (char 3) | 1205 |

In every cell and characteristic: `(x_a + x_b)D_{r,J} = 0` and `e_j D_{r,J} = 0` (`j` odd) hold exactly over `Z` modulo the box; `dim D_{r,J}C_r = r^{N/2}` and `dim I_JC_r = r^N − r^{N/2}` (all `J` for `N ≤ 4`, two `J` for `N ≥ 6`); the two sides of (ii) agree, also degree by degree after `d ↦ N(r−1) − d`; (iii) holds. For the cells with `N ≤ 8` and `r ≤ 7` the multipliers were ALL monomials (not only one variable per pair), so the check does not use (i).
Peak memory 115 MB, longest run 16 s, except `cold_T1c` (see «own errors»).

## E. Corollary 8.6 — HOLDS

- (i) re-derived line by line. Variables `x_0, y_1, …, y_{2k+1}`; the matchings of `{0, …, 2k+1}` are the `𝒥` of Theorem B. `D_{q−1}(a,b) = Σ_{u=0}^{q−2}(−1)^u a^u b^{q−2−u}` is literally the `D(a,b)` of §2.3, and `D_{q−1,J} = D(x_0, y_{k_0})·D_J` with `D_J` the product over the pairs avoiding `0`, as in Lemma 2.4 and Theorem B (same orientation `j_i < k_i`). `e_1 f = 0` on `M`; with `f = Σ_u x_0^u f_u`: coefficient of `x_0^u` (`u ≥ 1`) gives `f_{u−1} = −σf_u`, so `f_{r−1−j} = (−σ)^j f_{r−1}` and `θ` is injective. The coefficient of `x_0^{r−1}` in `D(x_0, y_{k_0})` is `(−1)^{r−1} = −1`, so `θ(D_{q−1,J}g) = −D_Jg`. `x_0D_{q−1,J} = −y_{k_0}D_{q−1,J}` gives `M = Σ_J D_{q−1,J}C`. So `θ(M) = (D_J : J)C` and `dim M = Q_k(q)` by Theorem B, over every field. `k = 0`: `N = 2`, one matching, `D_J = 1`, `M = D(x_0,y_1)C_{q−1}` of dimension `q − 1 = Q_0(q)`. Correct.
- My code (`cold_T2_theta.py`, `cold_T2.log`; 87 MB, < 1 s): at `(q, k) = (3,0), (3,1), (3,2), (5,0), (5,1), (7,1)` and characteristics `2, 3, 5, 1000003` (24 of 24): `dim M = rank θ(M) = dim (D_J)C = dim(θ(M) + (D_J)C) = Q_k(q)` (`2, 6, 20, 4, 36, 90`), and the recursion `f_{u−1} = −σf_u` holds on a basis of `M`.
- (ii) re-derived. It depends on exactly: Remark 8.4(6) for `q − 1 = 2m` and `n = N` even — that is [BRR, Proposition 2.12] with [BRR, Proposition 2.2], the simplicity of the natural module of `Sp_{2m}`, [Jan, II.4.21], and the dictionary (1) over an algebraically closed field, then base change; [Kos] (through [Gin]) in characteristic `0` (avoidable, see P5); Proposition 8.5(iii); Corollary 8.6(i), i.e. Theorem B; and the double annihilator in the box ring. Given `dim C/(e_odd) = Q_k(q)`: `M ⊆ ann(e_odd)` with equal dimensions, so equal; annihilators give `⋂_J I_JC = (e_odd)C`, and both ideals contain the box, so the equality lifts to `F[x]`. «Both inequalities of Proposition 9.1 are equalities»: correct (the left one is Theorem B).
- My code: the last two columns of the table of D. At the even box the ideals coincide in characteristics `3, 5, 1000003` at `(2,2), (2,4), (2,6), (2,8), (4,2), (4,4), (4,6), (6,4)` (24 of 24), and (ii) FAILS in characteristic `2` at the six cells with `N ≥ 4` (`8, 32, 128, 40, 544, 96` against `6, 20, 70, 36, 400, 90`), while (i) holds there.

## F. Remark 8.7 — HOLDS, with G1, E1, P4, P6, P7, P10

- (1) The right dual basis of `(x^u)` is `((−1)^u x^{r−1−u})`: `⟨x^{u'}, (−1)^u x^{r−1−u}⟩ = δ_{uu'}`. So `D_r = Σ_u x^u ⊗ (−1)^u x^{r−1−u}` is the canonical element, invariant under every isometry (also for the alternating form). The bold statement is a correct reading of Corollary 8.6, for the centralizer as an algebraic group (P4) and modulo [BRR] for its second half. The sentence on Proposition 2.5: P7.
- (2) Sketch: plausible; one false sentence (E1); `G^e` against `𝔤^e` (P10). It is labelled as a sketch here and in §13; in (3) the label is missing (P6(b)). My code agrees with its conclusion: at the odd box, `Σ_J D_{r,J}C_r = ann(e_odd)` at `(3,2), (3,4), (3,6), (5,2), (5,4), (7,4)` in characteristic `1000003`.
- (3) Statement correct for `char F ≠ 2`; the «`≤` over every field» is G1. The numbers: 30 pairs (cell, characteristic) and 4 cells in characteristic 2 agree with the logs (section I). My runs reproduce equality at `(3,2), (3,4), (3,6), (5,2), (5,4), (7,4)` in characteristics `2, 3, 5, 1000003` and at `(5,6)` in characteristics `2` and `3` (the cell `(5,6)` in characteristic 2 is not in the author's logs).
- The last sentence (14 of the 15 matchings, `q = 3`, `k = 2`, `F_3`: sum count `141`, intersection count `140`) is correct. My code (`cold_T6_subfamily.py`, `cold_T6.log`; 641 MB, 30 s): the intersection count is `140` for each of the 15 choices of the omitted matching; the sum count `dim F_3[x]/(E_K + (x_i^3))`, with `E_K = ⋂_{J∈K} I_J` computed degree by degree as the kernel of the restriction to the 14 spaces, is `141` for the three choices computed; the number of points is `141` in all 15.

## G. Over-claiming and under-claiming

Searched the paper for «Theorem A», «Kostant», «[BRR», «new», «adds», «know», «first time», «PLACEHOLDER», «present».
- **No leftover over-claim on Theorem A.** Abstract (line 19), §1.6 (line 99), Remark 8.3(2) (line 703), Remark 8.4 (title and (3)), §14 (line 946) all say that the count is not new and credit Kostant and [BRR]. The sentences of v9 that claimed the odd-characteristic count («what Theorem A adds is the same count in every odd characteristic») are gone. «Theorem A contains all of these» (Remark 8.3(2)) is a comparison with earlier results of the project and is followed at once by the disclaimer.
- The quotation of v9 in Remark 8.4(3) is exact (v9, Remark 8.4(3): «We do not know a version of Kostant's theorem in positive characteristic that gives this»).
- **Nothing is attributed to Kostant or [BRR] that they do not prove**, with the reservation that [Kos] was read only through [Gin] (the paper says so) and that [Gin] states the proposition for semisimple groups (E2).
- **Under-claims:** P1 (equality for every `μ`), P5 (in characteristic `0` [Kos] is not needed once [BRR] is used).
- **Over-claims by omission:** P4 (infinite field), E3 (the note's table), G1.
- Stale text: P2, P3.

## H. The note — HOLDS, with E1, E2, E3, G1, P1, P4, P12, P13

- §1: Lemma 1.1 and Proposition 1.2 re-derived (same steps as A, for both parities of `r`; `det f(e) = f(0)^r`, so `Z` for odd `r` and `{±1} × Z` for even `r`). Correct. Remarks (1)–(2) correct (exponents `1, 3, …, 2m − 1` of `B_m` and `C_m`).
- §2: same as B. The description of the proof of [BRR, 2.12] («free over `O(𝔱)`; fibre at `0`; fibre over the regular semisimple locus») is a fair summary of the proof as printed. §2.4 is commentary.
- §3: Proposition 3.1 correct (C). P13(a).
- §4: Proposition 4.1 and Theorem 4.2 are [CL, 8.5, 8.6]; correct. «so the lattice it spans over `Z` is saturated»: correct (the dimension of the span is the same over every `F_p`). §4.3: E1. §4.4 is a statement of ignorance, correctly labelled.
- §5: G1; P13(b). The counts agree with the logs.
- §6: recorded as a computation; not re-run. Two cells checked by hand: `(q, n) = (3, 2)`: `t^2(1 + t^{−1} + t^{−2})`, Hilbert series `1, 1, 1`; `(3, 3)`: `t^3(1 + 3t^{−1} + 2t^{−2} + t^{−3})`, Hilbert series `1, 2, 3, 1` (both agree with my computed series). «the Hilbert function … is the same in every characteristic `≠ 2` (by semicontinuity over `Z` and Theorem A)»: correct; my series agree in characteristics `3, 5, 1000003` at 14 cells.
- §7, Theorem 7.1: the propagation is correct given Lemma A.6, Theorem A.12, Theorem A.15 and Lemma A.3 as stated in the paper (see P1 for the induction, P12 for what should be written). Homogeneity: the generators `Θ^s_L(A;B)`, `e_j`, `x^q` are homogeneous, the rows are homogeneous, and `G_a/G_{a+1} ≅ (F[L]/R_a)(−a)`. Ties: rows with the same codimension are equal because the rows are nested.
  My code (`cold_T5_statistic.py`, `cold_T5.log`; 70 MB, 3 s): the Hilbert series of `F_p[L]/I_q(L)` equals `Σ_w t^{stat(w)}` at 14 cells `(q, n) = (3,2…7), (5,2…5), (7,2…4), (9,3)` in characteristics `3, 5, 1000003`, with two different rules for ties (84 of 84); e.g. `(3,6)`: `1, 5, 15, 29, 40, 36, 15`; `(5,5)`: `1, 4, 10, 19, 31, 41, 44, 36, 24, 10, 1`. The formula for `q = 3` holds for `n = 2, …, 7` (and I re-derived it: `stat = 2U − a_− + ℓ_1 = n − ℓ_0 − a_−`). The roots-of-unity identity holds at the 14 cells; its proof in characteristic `0` is correct.
- §8, the table: correct except the row of Theorem B (E3) and the two rows affected by P1.
- §9–§10: consistent with what the sources contain; the counts of §10 that have logs in this folder agree with them.

## I. Internal consistency

- Numbering and cross-references: Remark 8.4 has parts (1)–(6); every reference to 8.4(3), 8.4(4), 8.4(5), 8.4(6), to Proposition 8.5, Corollary 8.6(i)/(ii), Remark 8.7(1)–(3) and to problems 6–7 of §13 points to the right item (lines 107, 703, 742, 765, 893, 935, 936, 946–949, and the annotations of [GP], [Jan], [Mat], [Lus], [Liu], [Bry], [KLT], [Ric]). The row `C_r, D_r(a,b), D_{r,J}` of §1.9 is right. §1.8 describes v10 correctly, apart from P3.
- §12.5 against the logs of this folder: `generacion.log` has 28 lines OK (7 cells `(3,2), (3,4), (3,6), (5,2), (5,4), (7,4), (9,4)` × 4 characteristics) and was then stopped by the guard (`mem_kb=1360896`); `generacion_v2.log` has 22 of 22 (`(2,4), (2,6), (4,4), (4,6), (6,4)` × 4, and `(5,6)` in characteristics `3, 5`); `generacion_char2.log` has 9 of 9. So: 13 cells, 50 of 50, `(5,6)` in two characteristics only, 9 cells in characteristic 2, 30 pairs at the odd box and 4 odd cells in characteristic 2, one run stopped at `(5,6)` and rerun — all as stated in §12.5, in Remark 8.7(3) and in §5 and §10 of the note («1.36 GB» included).
- Not checkable from this folder (no logs here): «27 cells», «56 cycle types», «8 cells» of the even-`q` rings, «178 cells», and in the note «133 + 18», «24 + 16», «3 605», «6 cells», «5 cells».
- The author's engine `generacion_v2.py` (read after my runs) multiplies each `D_J` only by powers of one variable per pair; that is justified by Proposition 8.5(i). My runs with all multipliers give the same numbers.

## Own computations: summary, and own errors

All runs inside `vigia.sh` (1.2 GB, 10 min). Engines: `cold_lib.py` (own graded linear algebra modulo `p` in the box ring), `cold_T1_prop85_cor86.py`, `cold_T1c_cell56.py`, `cold_T2_theta.py`, `cold_T3_dictionary.py`, `cold_T5_statistic.py`, `cold_T6_subfamily.py`.

| run | what | peak | time | result |
|---|---|---|---|---|
| `cold_T1.log` | Prop 8.5, Cor 8.6, Rem 8.7(3): 11 cells × 4 characteristics | 28 MB | 2 s | FIN-OK |
| `cold_T1b.log` | cells (2,8), (7,4), (4,6) | 115 MB | 16 s | FIN-OK |
| `cold_T1c.log` | cell (5,6) | **1.30 GB — stopped by the guard** | 84 s | characteristics 2 and 3 done, 5 and 1000003 not run |
| `cold_T2.log` | the map `θ` | 87 MB | < 1 s | FIN-OK |
| `cold_T3.log` | dictionary; finite-field caveat; even `q` | 32 MB | 3 s | FIN-OK |
| `cold_T5.log` | note Thm 7.1; `K_(1)` | 70 MB | 3 s | FIN-OK |
| `cold_T6.log` | 14 of 15 matchings | 641 MB | 30 s | FIN-OK |

Own errors: (1) `cold_T1c`: I estimated 74 MB for the largest matrix and did not count the temporaries of my elimination routine nor the Python lists of rows; the guard stopped the run at 1.30 GB in the third characteristic. Not rerun; the two characteristics that finished are reported as such. (2) `cold_T6` peaked at 641 MB; I had not written an estimate before running it.

## What I did NOT check

- [Kos], [KLT], [Bry], [Lus], [Gra], [Jan], [Mat], [DCP] in the original. Inside [BRR] I read §2.1–§2.6 and followed the proof of Proposition 2.12, but I did not verify its inputs ([KLT, Theorems 2 and 7], [Co], [Lüb], [BMR]).
- The proofs of Theorem B (§5), of Theorem A (Appendix A: Lemmas A.8–A.10, Theorem A.12), of Proposition 2.5/2.6 and of Proposition 9.1; I used their statements.
- The computed claims without logs in this folder (listed in I), in particular Remark 8.4(5) beyond two cells by hand, and §6 of the note.
- The `.pdf` and `.html` renderings of the two documents; only the `.md` files were read.
- Whether the arXiv listing of [BRR] carries «, I» in the title (no web search was made).
- The statement of Remark 8.4(6) and of Corollary 8.6(ii) was checked numerically only up to `(r, N) = (4,6), (6,4), (2,8)`; the odd box up to `(5,6)` (two characteristics) and `(7,4)`.
- Everything in the paper outside the list of the commission (§2–§7, §10–§11, Appendix B) was not re-audited.
