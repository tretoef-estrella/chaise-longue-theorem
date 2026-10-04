# Literature sweep for version 12 (stage A, pending 429)

*Grepy Mandalay, 3 October 2026, 22:21–22:45 (Madrid). Written as it went. Status: lines 1–7 of the list done; six originals that four sentences of §8 would cite are owed and need Rafa's OK to download (§9). **No result that v11 claims as ours was found in the literature; the stop rule was not triggered.***

**Rule.** A result counts as read only when the original text was read (PDF through `pdftotext`, or the verbatim HTML of the paper), never an automatic summary. Every query is logged in `corpus4/regla313_literatura/QUERIES.md` with its date, its hit count and what was opened. That log is the «where we searched» of the paper.

**Verdicts.** `OURS, to the best of our knowledge` · `KNOWN: cite …` · `PARTLY KNOWN: …` · `NOT DECIDED: …` (with what is missing).

---

## 0. The table

| # | Result | Whose | Source read (file, page/line) | Where we searched | Verdict |
|---|---|---|---|---|---|
| 1 | Theorem O (odd box), every field, free over `Z` | ours | BRR, Riche, Liu (.tex, grep); Remark 10.7(2) of v11 | arXiv index, web, MathOverflow, 3 Oct (log, line 1) | **OURS** in char `p`; over `Q` a consequence of Kostant + first fundamental theorem (our sketch; not found written) |
| 2 | Corollary 10.8 (sum = intersection at the odd box) | ours | same | same | as row 1 |
| 3 | (F1)–(F7): Laplace expansions of Pfaffians and bordered Pfaffians | classical | — (originals owed, §9) | web, arXiv | **KNOWN**: cite Knuth / Ishikawa–Wakayama after reading |
| 4 | Lemma 8.7 (membership) and `Ω(ζ) = Ev(ζ) ∧ Od(ζ)` | ours | — | arXiv `bordered Pfaffians` 0 hits; web | **OURS** |
| 5 | Rank-two update of bordered Pfaffians (E9) | classical in form | — (originals owed, §9) | web | **KNOWN in form**: rank-two case of the Pfaffian sum formula (Stembridge 1990, Lemma 4.2; to read) |
| 6 | Conjecture 1.2 for every even `m ≥ 4` | ours | [DS] §5 (local, l. 1015–1035); Degtyarev 1512.06199 (local); all 11 citing papers (abstracts) | Semantic Scholar, OpenAlex, arXiv, web, 3 Oct | **OURS**; cells of [DS, §5] by computer are theirs |
| 7 | Conjecture 1.2 for every odd `m` (v7–v10) | ours | as row 6 | as row 6 | **OURS** (unchanged since v10) |
| 8 | Colour reduction (§6, §9.3) | ours; the splitting is standard | — | arXiv, web | **OURS** (splitting: standard) |
| 9 | Bipartite count (§7, Theorem C) | ours | — | arXiv, web | **OURS** |
| 10 | Cubic case with ballot paths (§4) | ours; ballot numbers classical | OEIS A039599 (cited); Specht ideals (abstracts) | web | **OURS**; cite two-row Specht ideals as nearest objects |
| 11 | Integral Hodge, Fermat quartic, dimension 2 | Mizukami 1975 | SSvL .tex l. 348, 1007, 1076 (local) | — | **KNOWN**: add Mizukami (via SSvL) |
| 12 | Integral Hodge, Fermat quartic, dimension 4 | AMV (computer); [DS, §5] | AMV text (local), Table 1 | — | **KNOWN** (v11 says so) |
| 13 | Integral Hodge, Fermat quartic, dimension 6 | [DS, §5] (primitivity) + the AMV argument | [DS] l. 1033; AMV Table 2 (linear lattice not computed) | — | **KNOWN** as a consequence (v11 says so) |
| 14 | Integral Hodge, Fermat quartic, dimension `≥ 8`; all prime `m`; Corollary H(ii) | ours | as above | arXiv `Fermat AND integral Hodge`, web, citations of [DS] | **OURS** |
| 15 | «Conjecture 1.2 + degree condition ⟹ integral Hodge» | AMV (I_2 empty), Aoki (degrees) | AMV l. 255–295, 1790–1810; Aoki p. 24 | — | **KNOWN**: v11 credits both |
| 16 | Condition «prime to `(n+2)!`» vs AMV's `(n+1)!` | — | AMV l. 260 | — | same condition for `k ≥ 1`; use AMV's form |
| 17 | (H4′), `m = 4` pair type | Aoki; SSvL for surfaces | Aoki p. 24; SSvL l. 479 | — | **KNOWN** (v11 credits Aoki) |
| 18 | Corollary W (partial Fermat varieties, every `m`) | implication [DS, Cor. 1.7]; unconditional ours | [DS] l. 189–195, 997–1018 | — | **PARTLY KNOWN**: implication theirs, statement ours |
| 19 | Lean: Main Theorem′ for every `m`; Pfaffians in Lean | ours | Mathlib `8f9d9cff` (grep); mathlib4 PRs; GitHub | GitHub API, web, 3 Oct | **OURS**; Mathlib has no Pfaffian; partial outside Mathlib: `Qsdd/Skewsymmetric` |
| 20 | Theorem A (count) | Kostant (char 0), BRR Prop. 2.12 (odd char) | v10 Remark 10.4 | 1 Oct | **KNOWN** (unchanged since v10); the dictionary and the elementary proof ours |

---

## 1. The odd box (Theorem O, Corollary 8.13, Corollary 10.8) — DONE, except the originals of four Pfaffian sources (§9)

**The statement.** For odd `r`, every field `F` and every `k`: `dim_F (D_J : J)·F[y_1, …, y_{2k+1}]/(y_i^r) = N_r(2k+2)`, with freeness over `Z` (Theorem O); in `2k+2` variables and characteristic `≠ 2`, `Σ_J D_{r,J}C_r = ann(e_j : j odd)` (Corollary 10.8).

**What the risk was.** Theorem A, which we had taken as ours, turned out to be Kostant (1963) in characteristic 0 and [BRR, Prop. 2.12] in odd characteristic. The odd box has the same number on the right, `N_r(2k+2)`, the dimension of the zero weight space of `V^{⊗(2k+2)}` for `SO_r`. So the question was: is the odd box a known statement about invariants of the regular unipotent centralizer, under another name?

**What we found.**
- **Characteristic 0: the count follows from classical theory, and v11 already says so.** Remark 10.7(2) of v11 sketches it: Kostant's theorem (evaluation at a regular nilpotent `e` maps the equivariant maps `𝔤 → W` onto `W^{G^e}`) plus the first fundamental theorem for `O_r` (the equivariant maps are spanned by contractions with the form) show that over `Q` the tensors `D_{r,J}` span the invariants of the centralizer, of the dimension of the zero weight space. We did not find this derivation written anywhere for tensor powers of the vector representation; its two ingredients are classical. Verdict: **PARTLY KNOWN — over `Q` a consequence of [Kos] and the first fundamental theorem (our sketch); the statement itself not found.**
- **Positive characteristic: not found.** The modular literature on the regular centralizer that the arXiv index returns (queries in the log) is [BRR], Riche 1411.3112 and Liu 2007.12444. All three are on disk; their sources contain no statement about tensors spanned by matchings or contractions (grep in the log). [BRR, Prop. 2.12] gives `dim W^{Z_G(u)} = dim W^T` for modules with a good filtration — the count of Theorem A, the *intersection* side — but nothing about which tensors span. Deriving Theorem O in characteristic `p` from good filtrations plus a characteristic-free first fundamental theorem (De Concini–Procesi) would be a new argument; v11 lists it as problem 7(a). Verdict: **OURS, to the best of our knowledge** (Theorem O for every field and its freeness over `Z`; Corollary 10.8 in characteristic `p ≠ 2`).
- **The ring `F[x]/(e_1, e_3, …; x_i^r)` and ideals of products over matchings.** Searched as ideals of odd elementary symmetric polynomials or odd power sums with truncation, divided-difference ideals, matching ideals, Specht ideals. Found: Specht ideals in the polynomial ring without the box (Yanagawa, Watanabe, McDaniel, Shibata; relevant to §4 at `q = 3`, see §4 below), regular sequences of power sums (Conca–Krattenthaler–Watanabe), orbit harmonics on matrix loci of involutions (Liu–Ma–Rhoades–Zhu 2409.06175). None is our ring or our ideal.
- **The Pfaffian machinery of §8.3.** Properties (F1)–(F7) are classical: the Laplace (minor summation) expansion of a Pfaffian and of a bordered Pfaffian. Candidate originals: Knuth, *Overlapping Pfaffians* (arXiv:math/9503234); Ishikawa–Wakayama, *Minor summation formulas of Pfaffians* (Linear Multilinear Algebra 39, 1995); Stembridge (Adv. Math. 83, 1990); Ishikawa–Okada (arXiv:math/0411280) for Pfaffians with entries `(x_j^n − x_i^n)/(x_i + x_j)`, of the type of our `D^−`. Verdict: **KNOWN: cite a classical source for (F1)–(F7)** (which one, after reading; §9).
- **Lemma 8.7 (membership) and the decomposability `Ω(ζ) = Ev(ζ) ∧ Od(ζ)`**: not found. **OURS, to the best of our knowledge.**

## 2. The even degrees of Conjecture 1.2; papers citing [DS] — DONE

- Every paper that cites [DS] (Semantic Scholar: 10; OpenAlex: 11 for the journal version, 4 for the arXiv version; union in the log) was identified and its abstract read. None proves Conjecture 1.2 in a new case. Degtyarev 1512.06199 (local original) restates it as open (Conjecture 4.4).
- What was known for even `m`: [DS, §5] confirmed it by computer at `(n, m) = (4, m)` with `3 ≤ m ≤ 12` (so at `m = 4, 6, 8, 10, 12` in dimension 4) and at `(6, 4)` (local original, lines 1015–1035). v11 §1.1 and §9 already say this.
- Verdict: **the even degrees `m ≥ 4`, `k ≥ 1`, as a theorem: OURS, to the best of our knowledge.** The cells of [DS, §5] are theirs, by computer.
- **To note for Rafa (not a paper):** the issue *google-deepmind/formal-conjectures #6662*, opened by Rafa on 28 September 2026, proposes Conjecture 1.2 and says «the case of even `m` remains open». It is open, with no comments. After v12 is released it is out of date; whether to add a comment there is Rafa's decision.

## 3. Integral Hodge for Fermat quartics; the `(n+2)!` clause — DONE

- **The implication «Conjecture 1.2 ⟹ integral Hodge» in these degrees is not ours.** AMV state the condition «`d` prime, or `d = 4`, or `gcd(d, (n+1)!) = 1`» and note that under it «`I_2` is the empty set», so that the linear cycles generate rationally all Hodge classes (AMV §1 and §3, local original). The degree set is Aoki's Theorem A [Aok, p. 24]. v11 credits both (§1.3, §12, (H5)).
- **The quartics.** Dimension 2: Mizukami 1975, as reported by Schütt–Shioda–van Luijk (SSvL, `.tex` lines 348, 1007, 1076: «for `m = 4` … unknown until Mizukami in 1975 proved the affirmative»). **v11 cites [SSvL], [De14] for `m = 4`, `k = 1`; v12 should add Mizukami as the original** (we have not read Mizukami's paper; cite it through SSvL and say so). Dimension 4: AMV, by computer (Table 1 includes `(4, 4)`), and [DS, §5]. Dimension 6: [DS, §5] confirms primitivity at `(6, 4)`; AMV's Table 2 lists the Hodge lattice at `(6, 4)` but says the linear lattice was not computed there. Dimension `≥ 8`: not found.
- Verdict: **integral Hodge for the Fermat quartic in every even dimension `2k ≥ 8`: OURS, to the best of our knowledge** (v11 says exactly this, §1.3 «What was known»). Also ours: the uniform statement for every prime `m`, and every cell of Corollary H(i) with `m` not prime and `k ≥ 2`; Corollary H(ii) for `k ≥ 2`.
- **The clause «prime to `(n+2)!`».** AMV write `gcd(d, (n+1)!) = 1`, with `n` the dimension; v11 §1.3 writes «every prime factor of `m` is at least `2k + 3`» and says it is the same as `gcd(m, (n+2)!) = 1` and as AMV's condition, for odd `m`. Check: with `n = 2k`, «every prime factor of `m` is at least `2k + 3`» means that no prime `≤ n + 2` divides `m`, i.e. `gcd(m, (n+2)!) = 1`. And `gcd(m, (n+2)!) = 1 ⟺ gcd(m, (n+1)!) = 1`, because the only extra factor `n + 2 = 2k + 2` is even and, for `k ≥ 1`, not prime, so it brings no new prime. **The two conditions are the same for every `m` and every `k ≥ 1`.** The title of v11 says «prime to `(n+2)!`»; AMV say `(n+1)!`. **Recommendation for v12:** use AMV's `(n+1)!` in the title and say once that it is the same condition.
- **New papers to cite in v12 as related work (rational Hodge, complementary):** Miranda–Movasati–Rufino–Villaflor, *Lengths of Hodge characters in Fermat varieties*, arXiv:2609.27301 (23 Sep 2026; rational Hodge conjecture for all Fermat varieties of degree `< 65`, except `44, 51, 52`); Favero–Kelly, arXiv:2609.12759 (11 Sep 2026; the Hodge conjecture for the degree-33 Fermat fourfold); da Silva, arXiv:2101.04739. Jumagulov 2608.18134 is already cited. (Abstracts read; full texts not read.)

## 4. Colour reduction, bipartite count, rank-two update, membership lemma, explicit Pfaffian signs — DONE, except the originals of §9

- **The splitting of Lemma 6.1** (the group algebra of the part of `G` prime to `p` is split semisimple over a field with enough roots of unity, so `F[G]` is a product over its characters): **KNOWN, standard** (Maschke and the Chinese remainder theorem). v12 should say «standard» in one clause; no single paper is owed.
- **The colour reduction of §6 and §9.3** (the use of that splitting to reduce [DS, Conjecture 1.2] to a product of bipartite and odd-box counts): not found. **OURS, to the best of our knowledge.**
- **The bipartite count (§7, Theorem C, Theorem 7.6)**: not found under any of the names searched (matching ideals, divided-difference ideals, products over matchings, truncated polynomial rings). **OURS, to the best of our knowledge.**
- **The cubic case (§4, Theorem 4.1, ballot paths)**: the theorem is ours; the ballot numbers are classical (OEIS A039599, cited), and Remark 4.2(3) already cites James for the Specht-module reading. Related but different: the Specht ideals of two-row shapes in the polynomial ring, without the box (Yanagawa; Watanabe–Yanagawa 1712.04262; McDaniel–Watanabe 2103.00759; Shibata–Yanagawa). v12 may cite them in Remark 4.2(3) as the nearest objects in the literature.
- **The rank-two update of bordered Pfaffians** (`bpf(a − (E·Oᵀ − O·Eᵀ); c) = bpf(a; c) + bpf(a; c, E, O)`, Lean piece E9). **KNOWN in form**: it is the special case, for a matrix `B` of rank two, of the expansion of the Pfaffian of a sum `Pf(A + B) = Σ_I ± Pf(A_I)·Pf(B_{I^c})`, since only the pairs `I^c` contribute when `B` has rank two. That expansion is classical (it is attributed to Stembridge 1990, Lemma 4.2, and to Ishikawa–Wakayama 1995; **not yet read in the original**, §9). The use of it to prove the membership lemma: ours.
- **The membership lemma (Lemma 8.7) by the route without the exterior algebra** (E10: Laplace expansion, Vandermonde divisibility over any commutative ring): the ingredients are classical (an alternating polynomial is divisible by the Vandermonde product); the lemma is **OURS, to the best of our knowledge.**
- **The explicit signs of §8.3**: sign conventions of classical expansions; nothing to attribute beyond the classical source of (F1)–(F7).

## 5. Corollary 10.8, (H4′), Corollary W — DONE

- **Corollary 10.8** (sum equals intersection of the matching ideals at the odd box): see §1. Over `Q` a consequence of [Kos] and the first fundamental theorem (Remark 10.7(2) of v11); in characteristic `p ≠ 2`: **OURS, to the best of our knowledge.**
- **(H4′)** (for `m = 4` every Hodge character is of pair type): the case `m = 4` of Aoki's Theorem A [Aok, p. 24] (local original, OCR), and for surfaces also SSvL (`D_m = B_m ⟺ m ≤ 4 or (m, 6) = 1`, `.tex` line 479). **KNOWN**; the three-line proof in v11 is ours and elementary, and v11 already credits Aoki.
- **Corollary W** (the subspaces of [DS] on the partial Fermat varieties `W_s` span primitive sublattices). The implication «Conjecture 1.2 in dimension `2s` ⟹ primitivity on `W_s`» is [DS, Corollary 1.7] (local original, lines 189–195, proof §4.6, lines 997–1018; they deduce it unconditionally only for `s = 0, 1`). **The implication is theirs; the unconditional statement for every `m` and every `s` is ours**, as v11 says.

## 6. Formalization — DONE

- **Mathlib has no Pfaffian.** Searched: the Mathlib version of our project (commit `8f9d9cff`, 16 Feb 2026) — no file mentions «pfaffian»; the pull requests and issues of `leanprover-community/mathlib4` (GitHub API, query `pfaffian`) — one hit, about symplectic matrices, none defining a Pfaffian.
- **Other Lean work found:** `Qsdd/Skewsymmetric` (a partial formalization of skew-symmetric matrices and Pfaffians, outside Mathlib, updated April 2026); `Li-Hongmin/hodge-odd-fermat-fourfolds` (Lean certificates for the finite arithmetic endpoints of an AI-generated proof of the *rational* Hodge conjecture for odd-degree Fermat fourfolds, September 2026; their README says the main theorems are not formalized); `rifmj/fermat-fourfolds-boundary` (Jumagulov's package, with a Lean part). The DeepMind repository `formal-conjectures` contains no statement about Fermat varieties; it has Rafa's open issue #6662.
- **No formalization of results of the kind of [DS] or of the Main Theorem was found** (searches: GitHub repositories for `pfaffian` in Lean, `fermat variety lean`, `lean4 pfaffian`, `hodge conjecture lean`, `group ring torsion free lean`; a web search including the Archive of Formal Proofs and Coq; queries in the log).
- Verdict for the certificate: **«to the best of our knowledge, the first machine-checked proof of a case of Conjecture 1.2,»** is defensible; v12 and the certificate should say «to the best of our knowledge» and name `Qsdd/Skewsymmetric` as a separate partial formalization of Pfaffians.

## 7. Anything else — DONE

- **Orbit harmonics.** Replacing an ideal of points by the ideal of its top-degree forms (`gr I`) is the method that the combinatorics literature calls *orbit harmonics* (Liu–Ma–Rhoades–Zhu 2409.06175 and the papers it cites). Wherever v12 uses leading forms of a point ideal as a method, one sentence can name it. Not a priority claim.
- **Rational Hodge for Fermat fourfolds, related and complementary:** Kang (Bull. Aust. Math. Soc. 93, 2016, Corollary 3.2, quoted in Li's README and in 2609.27301; not read), Miranda–Movasati–Rufino–Villaflor 2609.27301, Favero–Kelly 2609.12759, Li (AI-generated preprint, DOI 10.13140/RG.2.2.26853.77288, September 2026), Jumagulov 2608.18134 and its even-degree companion. All rational; none about the lattice `L(X)` over `Z`.
- **Lehrer–Zhang 1207.5889** (Brauer category): the first and second fundamental theorems for `O(V)` and `Sp(V)` in characteristic zero only (abstract read). The characteristic-free first fundamental theorem is De Concini–Procesi 1976 (read in the original on 18 September 2026; the local copy is in the folder of the Steinberg sources). These are the ingredients that problem 7(a) of v11 would need; neither states our result.

---

## 8. Sentences for v12 and for the README

**Where we searched (to go in v12 §1.8 or a new «Literature» paragraph, and in the README):**

> *Before this version we searched the literature for each result that we call new: the arXiv index (titles and abstracts) and its listings; Google Scholar and the open web; the citations of [DS] in Semantic Scholar and OpenAlex; the publication lists of the authors of [DS]; MathOverflow; and GitHub, including Mathlib and the `formal-conjectures` repository, for formalizations. The queries, their dates and their results are recorded in [Rep], `record/literature/`. The sources that decide attributions were read in the original.*

**The odd box (§8, and Remark 10.7):**

> *Over `Q`, Theorem O and Corollary 10.8 can be derived from Kostant's theorem and the first fundamental theorem of invariant theory for `O_r` (Remark 10.7(2)); we did not find this derivation written. In positive characteristic we did not find Theorem O, or the statement that the tensors `D_{r,J}` span the invariants of the centralizer, in the literature, in particular not in [BRR], [Ric] or [Liu]. To the best of our knowledge, after the search described in §1.8, Theorem O and Corollary 10.8 are new in positive characteristic.*

**The even degrees (§1.1):**

> *To the best of our knowledge, after the search described in §1.8, no proof of Conjecture 1.2 for an even degree `m ≥ 4` and `k ≥ 1` had appeared before this paper, beyond the cells confirmed by computer in [DS, §5].*

**Quartics (§1.3), one change:** *«For `m = 4`, at `k = 1` … which is known [SSvL], [De14]»* → add *«it was first proved by Mizukami (1975), as recorded in [SSvL, §1 and §6]»* (we did not read Mizukami's paper).

**Title and §1.3:** replace «prime to `(n+2)!`» by «prime to `(n+1)!`», AMV's form, and keep the sentence that the conditions coincide (they do for every `k ≥ 1`, §3 above).

**Related work (§1.3, after Jumagulov):** cite Miranda–Movasati–Rufino–Villaflor 2609.27301 and Favero–Kelly 2609.12759 (rational Hodge, complementary), after reading them (§9).

**The Pfaffians (§8.3):** *«Properties (F1)–(F7) are classical; see [Knuth] and [IW] (Laplace expansion of Pfaffians and bordered Pfaffians).»* and, at the rank-two update if v12 prints the shorter route of §8.5: *«this is the case of rank two of the expansion of the Pfaffian of a sum, [Ste, Lemma 4.2]»* — after the originals are read (§9).

**Formalization (§14.8 and the certificate):** *«To the best of our knowledge this is the first machine-checked proof of a case of Conjecture 1.2 of [DS]. Mathlib has no Pfaffian; we defined Pfaffians and bordered Pfaffians in our project. A separate partial formalization of Pfaffians exists outside Mathlib (`Qsdd/Skewsymmetric` on GitHub).»*

---

## 9. What is still owed (needs Rafa's OK to download)

The verdicts above do not depend on these files, but four sentences of §8 cite them, and the rule is to cite only what was read in the original. One batch, from arXiv (sizes from a `HEAD` request; nothing was downloaded):

| File | Source | Size | For |
|---|---|---|---|
| Knuth, *Overlapping Pfaffians* | arxiv.org/pdf/math/9503234 | 128 450 bytes | (F1)–(F7), history of Pfaffians |
| Baik–Rains, *Algebraic aspects of increasing subsequences* | arxiv.org/pdf/math/9905083 | 437 286 bytes | bordered Pfaffians `pf(v; A)`; the rank-two update |
| Ishikawa–Okada–Tagawa–Zeng, *Generalizations of Cauchy's determinant and Schur's Pfaffian* | arxiv.org/pdf/math/0411280 | 330 651 bytes | Pfaffians with entries of the type of `D^−` |
| Okada, *Pfaffian formulas and Schur Q-function identities* | arxiv.org/pdf/1706.01029 | 230 830 bytes | the Pfaffian sum formula and its sources |
| Miranda–Movasati–Rufino–Villaflor, *Lengths of Hodge characters in Fermat varieties* | arxiv.org/pdf/2609.27301 | 539 713 bytes | related work, §1.3 |
| Favero–Kelly, *The Chern character of a coherent sheaf on a smooth projective hypersurface* | arxiv.org/pdf/2609.12759 | 438 302 bytes | related work, §1.3 |

Not on arXiv, and not needed if the above suffice: Stembridge, Adv. Math. 83 (1990); Ishikawa–Wakayama, Linear Multilinear Algebra 39 (1995); Mizukami (1975); Kang (2016).


---

## 10. The six originals, read (3 Oct 2026, 23:30–23:50, after Rafa's OK)

Downloaded to `FUENTES_ORIGINALES_V12_2026-10-03/` (manifest with md5 there); read in the original with `pdftotext`. What each one gives, and what v12 may cite.

| Source | What we read | What v12 cites it for |
|---|---|---|
| Knuth, *Overlapping Pfaffians*, Electron. J. Combin. 3(2) (1996) #R5, arXiv:math/9503234 | (0.1) definition as a sum over perfect matchings with the sign of the permutation; (0.4) an odd permutation reverses the sign; (2.0) expansion of `f[β]` along any element `x ∈ β`; §3 determinants as the bipartite special case of Pfaffians; §6 history (Pfaff 1815, Jacobi 1827, Cayley 1849). | (i)–(iii) of §8.3 and (F1)–(F4): «classical, see [Knu, (0.1), (0.4), (2.0) and §3]». |
| Okada, *Pfaffian formulas and Schur Q-function identities*, Adv. Math. 353 (2019) 446–470, arXiv:1706.01029 | §2.1: multilinearity in a row-and-column, `Pf(UᵀXU) = det U·Pf X`, alternation under permutations, expansion (2.4) along the `k`-th row with explicit signs `(−1)^{k+i−1}`. **Proposition 2.3**: for `[[Z, W], [−Wᵀ, Z']]`, `Pf = Σ_{I,J} ε(I,J) Pf Z(I) Pf Z'(J) det W([m]∖I; [n]∖J)`, with explicit `ε`; Okada states it was given without proof in Caianiello (1959) and proves it. | (F7) of §8.3 is the case `Z' = 0` of [Oka, Prop. 2.3] (only `J = ∅` survives). (F2): multilinearity [Oka, §2.1]. |
| Baik–Rains, *Algebraic aspects of increasing subsequences*, arXiv:math/9905083 | §6: the notation `pf(v; A)` for a Pfaffian bordered by `v` (6.2); de Bruijn's formula (Theorem 6.1); a rank-two simplification by row and column operations in a specific matrix (around (6.23)). | Optional, for the term «bordered Pfaffian» only. It does **not** contain our rank-two update. |
| Ishikawa–Okada–Tagawa–Zeng, *Generalizations of Cauchy's determinant and Schur's Pfaffian*, Adv. in Appl. Math. 36 (2006) 251–287, arXiv:math/0411280 | Abstract, §1, Theorem 1.1: Schur-type Pfaffians whose entries are quotients of generalized Vandermonde determinants. | Nothing. Our entries `D^−(a, b) = (b^{r−1} − a^{r−1})/(a + b)` are of a related shape, but no statement of theirs is used. Not cited. |
| Miranda–Movasati–Rufino–Villaflor, *Lengths of Hodge characters in Fermat varieties*, arXiv:2609.27301 (v2, 26 Sep 2026) | Abstract and §1: the (rational) Hodge conjecture for Fermat varieties of every dimension and every degree `d < 65`, `d ≠ 44, 51, 52`, by length reduction in Aoki's module of tuples and Kang's theorem for fourfolds. They record that the conjecture was known for `d ≤ 20` (Shioda), `d` a prime power or twice a prime power (Aoki), `d = 21` (da Silva Jr.). The word «integral» does not occur in the sense of the integral Hodge conjecture; they do not cite [DS]. | Related work in §1.3: rational Hodge; complementary to Corollary H (integral). |
| Favero–Kelly, *The Chern character of a coherent sheaf on a smooth projective hypersurface*, arXiv:2609.12759 (11 Sep 2026) | Abstract and §1: an explicit Čech-cocycle formula for the Chern character via matrix factorizations; the (rational) Hodge conjecture for the degree-33 Fermat fourfold. | Related work in §1.3, next to the previous one. |

**Verdicts that change.**

1. **The Pfaffian sum formula `Pf(A + B) = Σ ± Pf(A_I)·Pf(B_{I^c})` is in none of the four Pfaffian originals read.** So v12 does **not** write «the rank-two update is [Ste, Lemma 4.2]» (Stembridge not read). It says: *«We give a direct proof (Lemma 8.x, checked in Lean); identities of this kind are classical, but we have not traced this one to a source we have read.»*
2. **(F7) has a source read in the original: [Oka, Prop. 2.3]** (with `Z' = 0`), which itself attributes the formula to Caianiello (1959, not read).
3. **Related work is complementary.** Both September 2026 papers are about the rational Hodge conjecture; neither touches Conjecture 1.2 or the integral Hodge conjecture. Stop rule: not triggered.
4. Mizukami (1975), Stembridge (1990), Ishikawa–Wakayama (1995), Kang (2016), Caianiello (1959): not read; cited only through the sources that record them, saying so.

*— Grepy Mandalay, 3 Oct 2026, 23:50.*

**Correction (4 Oct 2026, 00:05, checked in the original `FUENTES_ORIGINALES_WATERMARK_2026-09-30/SSvL_fermat-2009.tex`).** §8 above wrote «[SSvL, §1 and §6]». The places are **§3** (line 348: «unknown until Mizukami in 1975 proved the affirmative») and **§6** (Proposition «[Mizukami, Inose]», line 1075: «The complex Fermat quartic surface has Néron–Severi group generated by lines. Its discriminant is −64»). SSvL's reference: M. Mizukami, *Birational mappings from quartic surfaces to Kummer surfaces* (in Japanese), Master's thesis, University of Tokyo, 1975. v12 cites it in this form.
