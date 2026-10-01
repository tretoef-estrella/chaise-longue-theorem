# Theorems — a guide for referees and future readers

This page is a map. It lists the statements a referee needs, in the order in which the proof uses them, with the section of the [paper](paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) where each is proved and the engine that corroborates it. It then lists the results of the campaign that stand on their own, the results of the earlier Hodge–Fermat campaign that the paper cites, and — just as useful — the statements in the record that are **false**, so that nobody builds on them.

**Notation.** $X$ is the Fermat variety $z_0^m + \cdots + z_{n+1}^m = 0$ of dimension $n = 2k$; $\mathcal{J}$ is the set of the $(2k+1)!!$ perfect matchings of $\{0, \dots, 2k+1\}$; $q = p^v$ is an odd prime power; $C = \mathbb{F}_p[y_1, \dots, y_{2k+1}]/(y_i^{q-1})$; $D(a,b) = (b^{q-1} - a^{q-1})/(a+b)$ and $D_J$ is the product of $D$ over the pairs of $J$ not containing $0$; $Q_k(q) = (2k+2)!\,[x^{2k+2}]\,I_0(2x)^{(q-1)/2}$.

---

## 1. The chain of the proof

| # | Statement | What it says | Paper | Corroborated by |
|---|---|---|---|---|
| 1 | **Theorem 0** [DS] | the results of Degtyarev–Shimada that turn Conjecture 1.2 into algebra: the torsion of $H_n(X)/L(X)$ is that of $\mathbb{Z}[G]/(\psi_J)$, the upper bound (a Chinese-remainder count), and the rank | §2, Appendix B | — (quoted; Appendix B re-derives it modulo Pham's theorem and [DS, Thm 2.2]) |
| 2 | **Proposition 2.1** | torsion freeness at $m$ ⟺ one dimension count over $\mathbb{F}_p$ for each prime $p \mid m$; the inequality $\ge$ always holds | §2.1 | — |
| 3 | **Lemmas 2.3–2.4**, **Proposition 2.5** | the change of variable $y = t - t^{-1}$ turns each generator into $\text{unit}\cdot Y\cdot D_J$, so at $m = q$ the conjecture is **(S)**: $\dim_{\mathbb{F}_p}(D_J : J \in \mathcal{J})\,C = Q_k(q)$ | §2.3–§2.4 | `engines/v7-verification/theorem-b-and-translation/regla268_sumform.py`, `regla264_ds.py` |
| 4 | **Theorem 4.1** | the cubic case $q = 3$, with an explicit basis of ballot paths | §4 | `regla270_q3_specht.py` |
| 5 | **Lemma 5.1** | peeling: slice the ideal by the powers of $y_1$, and the point set by the fibres of the projection | §5.1 | — |
| 6 | **Lemma 5.2** | the root: the full family of matchings enters here, and only here | §5.2 | — |
| 7 | **(P1), Lemma 5.5 (chain)** | the fibre sizes depend only on a partition; the possible new values form one chain for weak dominance | §5.4–§5.5 | `regla270_gate1_downsets.py` |
| 8 | **Proposition 5.6 (P2)** | the layers are again down-sets — **the only real case analysis of the proof** | §5.6 | `regla269_p2.py`, `regla270_gate1_downsets.py` |
| 9 | **Proposition 5.8 (P3)** | every generator of a layer lifts to the right slice, with no slack | §5.7 | `regla270_gate2_dims.py` |
| 10 | **Theorem 5.3** | $\dim V_\Lambda \ge \lvert Z_\Lambda\rvert$ for every down-set $\Lambda$, every field, every odd $q$ | §5.3, §5.8 | `regla270_gate2_dims.py` |
| 11 | **Theorems 5.9, 5.9′** | equality in every characteristic, and freeness over $\mathbb{Z}$ | §5.9 | `regla276_igualdad.py`, `regla278_*.py` |
| 12 | **Theorem B** = Corollary 5.4 | (S) for every $k$ and every odd $q$ ⟹ the conjecture for $m = p^v$ | §5 | `regla274_S_primo_p.py`, `regla275_S_cualquier_cuerpo.py` |
| 13 | **Lemmas 6.1–6.8**, **Proposition 6.9** | for $m = q\cdot r$ with $p \nmid r$, the group algebra splits over colourings by $r$-th roots of unity; each factor is a tensor product of blocks | §6 | `engines/composite-degrees-auditor/`, `engines/v7-verification/main-theorem-prime/ejemplo_15.py` |
| 14 | **Theorem C**, **Theorem 7.6**, **Proposition 7.4** | the bipartite blocks, counted by the same method with pairs of partitions; Proposition 7.4 is the second case analysis | §7 | `engines/fable-composite-degrees/`, `engines/composite-degrees-auditor/` |
| 15 | **Corollary 7.7** | **Main Theorem′ and the Main Theorem** | §7.7 | `engines/v7-verification/main-theorem-prime/gate_mainprime.py` |

The whole chain uses no computer. The engines are corroboration: they test every intermediate statement on every case small enough to enumerate, with negative controls that fire when a hypothesis is removed (§12 of the paper, and [HOW_TO_VERIFY.md](HOW_TO_VERIFY.md)).

## 2. Consequences proved in the paper

| Statement | What it says | Paper |
|---|---|---|
| **Corollary H** | for $m$ an odd prime, or every prime factor of $m$ at least $2k+3$: $\mathrm{Hdg}(X) = L(X)$, so the integral Hodge conjecture holds for $X$; for every other odd $m$, $L(X)$ is primitive in $\mathrm{Hdg}(X)$ with a free complement of rank $\lvert\mathfrak{B}\rvert - Q_k(m)$ | §10 |
| **Lemma 10.4** | for $m = 9$ that rank is $\binom{2k+2}{k+1}^3 - Q_k(9)$: $48,\ 2\,880,\ 152\,880,\ 8\,064\,000$ for $k = 1,\dots,4$ | §10.3 |
| **Corollary W** | on the partial Fermat varieties $W_s$, the $(2s+1)!!\,m^{d+1}$ linear spaces of [DS] span a primitive sublattice — [DS, Corollary 1.7], until now conditional on Conjecture 1.2 | §11 |
| **Corollary 7.8** | over $\overline{\mathbb{F}}_p$ the bipartite counts are equalities | §7.7 |
| **Theorem A** | $\dim_F F[x_1,\dots,x_n]/(e_1, e_3, e_5, \dots;\ x_i^q) = n!\,[y^n]\,e^y I_0(2y)^{(q-1)/2}$ for every field of characteristic $\ne 2$ and every odd $q$; with Corollaries 8.1–8.2. **A different statement from the conjecture.** **As a count it is not new:** it follows from Kostant's theorem (1963) in characteristic 0 and from Bezrukavnikov–Riche–Rider (arXiv:2005.05583, Proposition 2.12) in odd characteristic, through the dictionary of Remark 8.4 (version 10); the paper's contribution is that dictionary and an elementary proof | §8, Appendix A |
| **Fact 9.2** | for the subfamily $K = \mathcal{J} \setminus \{2 \text{ matchings}\}$ at $q = 9$, $k = 2$: $\dim = 4\,730 < 4\,736 = \lvert\Gamma_K\rvert$. The conjecture's analogue fails for subfamilies; the full family is needed | §9.2 |

## 3. The constructions and their audits

The three proofs that close the conjecture were written by external Claude instances with their own engines, and audited cold before the paper was written:

- **Theorem D** (the conjecture for $m = 3^v$, the first form of Theorem B): constructed in the 15th *Chessboard* mission — [engines/fable-chessboard/INFORME_15.md](engines/fable-chessboard/INFORME_15.md); cold audit: [record/audits/cold-audit-of-theorem-D.md](record/audits/cold-audit-of-theorem-D.md).
- **Theorem Γ** (the count of Theorem A for $q = 3^v$): [engines/fable-chessboard/INFORME_14.md](engines/fable-chessboard/INFORME_14.md); audit: [record/audits/audit-of-theorem-A.md](record/audits/audit-of-theorem-A.md).
- **The degrees that are not prime powers** (§6–§7): [engines/fable-composite-degrees/INFORME_1.md](engines/fable-composite-degrees/INFORME_1.md); audit: [record/audits/audit-of-the-composite-degrees.md](record/audits/audit-of-the-composite-degrees.md).

## 4. Results of the campaign that stand on their own

Selected from the [222 standalone documents](theorems/INDEX.md) for their interest outside this proof. The grade is the one the campaign's own audits recorded; **none of these has been refereed**, and none is used by the paper.

| Result | Grade in the record | File |
|---|---|---|
| **The Hinge Lemma** — fixing one pair of coordinates restricts the generating series of level $k$ to that of level $k-1$ times the factor $(1 - v^2 w)$ | proved for every $k$ (pencil), machine-gated | [CHAISE_LONGUE_HINGE_LEMMA.md](theorems/standalone/CHAISE_LONGUE_HINGE_LEMMA.md) |
| **The Odd Symmetric Theorem** — for six indices, $\bigcap_J I_J = (e_1, e_3, e_5)$, a reduced complete intersection of degree $15$ whose components are exactly the fifteen matching planes | proved (characteristic $\ne 2$), audited four times | [THE_ODD_SYMMETRIC_THEOREM.md](theorems/standalone/THE_ODD_SYMMETRIC_THEOREM.md) |
| **The Matching Lattice Shellability Theorem** — the intersection lattice of the matching arrangement is CL-shellable | proved for every $k \ge 1$, characteristic $\ne 2$ | [CHAISE_LONGUE_MATCHING_LATTICE_SHELLABILITY_THEOREM.md](theorems/standalone/CHAISE_LONGUE_MATCHING_LATTICE_SHELLABILITY_THEOREM.md) |
| **The Letter Census Theorem for $B_m$** — a closed form for the census series of the letter $B_m$ | proved for every $m$ | [CHAISE_LONGUE_LETTER_CENSUS_THEOREM_BM.md](theorems/standalone/CHAISE_LONGUE_LETTER_CENSUS_THEOREM_BM.md) |
| **The Graded Pinning Theorems** (S, NZD, SYZ, GP) | proved for every $k$ (pencil), machine-gated $k \le 4$ | [CHAISE_LONGUE_GRADED_PINNING_THEOREM.md](theorems/standalone/CHAISE_LONGUE_GRADED_PINNING_THEOREM.md) |
| **The $q = 3$ Socle Law** | proved uniformly in $k$, modulo four textbook citations (later read in the original) | [CHAISE_LONGUE_Q3_SOCLE_LAW_THEOREM.md](theorems/standalone/CHAISE_LONGUE_Q3_SOCLE_LAW_THEOREM.md) |

## 5. The Hodge–Fermat campaign (May–June 2026)

The paper cites these as [Rep]. They concern the lattices of Fermat varieties and surfaces, computed from the Degtyarev–Shimada criterion on an 8 GB laptop. The campaign's own account is its [README](hodge-fermat-campaign/README.md); the grades below are the ones it states.

| Result | What it establishes | File |
|---|---|---|
| **The Watermark Theorem** (4 June 2026) | the discriminant of the lattice of linear Hodge cycles of the Fermat surface of degree $m$; the odd-prime half proved — the case $k = 1$ of open problem 3 of the paper | [md](hodge-fermat-campaign/THE_WATERMARK_THEOREM.md) · [pdf](hodge-fermat-campaign/THE_WATERMARK_THEOREM.pdf) · the law: [md](hodge-fermat-campaign/THE_WATERMARK_LAW.md) · **verified in Lean 4:** [certificate](hodge-fermat-campaign/LEAN_CERTIFICATE_WATERMARK_v2.pdf) |
| **The Double Ladder Theorem** (5 June 2026) | the discriminant *group* of the Néron–Severi lattice of a prime-degree Fermat surface: structure, not just order (version 4, 30 September 2026: corrections on the published tables and on Shioda's question; proved for every prime by order, exponent and rank — see the notes in the [campaign README](hodge-fermat-campaign/README.md)) | [md](hodge-fermat-campaign/THE_DOUBLE_LADDER_THEOREM.md) · [pdf](hodge-fermat-campaign/THE_DOUBLE_LADDER_THEOREM.pdf) · **verified in Lean 4:** [certificate](hodge-fermat-campaign/LEAN_CERTIFICATE_DOUBLE_LADDER_v2.pdf) |
| **The Watermark in Every Even Dimension** (1 October 2026) | the discriminant of the Hodge lattice of a Fermat variety of prime degree $p$ in every even dimension $2k$ — the discriminant half of open problem 3 of the paper (the elementary divisors stay open): the discriminant group is the ring $\mathbb{Z}[G]/(I_{\mathfrak B} + I_T)$ (every degree $m \ge 3$), and $\lvert\operatorname{disc}\rvert = p^{E_k(p)}$ with $E_k(p)$ read off the Hilbert function of the Theorem-A ring with the even box $p-1$ (in general modulo a count that follows from Bezrukavnikov–Riche–Rider; a proved lower bound without it; checked by machine in 22 cells). Read cold before release; not verified in Lean | [repository](https://github.com/tretoef-estrella/watermark-theorem#in-every-even-dimension-1-october-2026) · [pdf](https://github.com/tretoef-estrella/watermark-theorem/blob/main/papers/THE_WATERMARK_IN_EVERY_EVEN_DIMENSION.pdf) · [Zenodo](https://doi.org/10.5281/zenodo.23091045) |
| **The Localization Theorem** | the torsion is localized to a single Chinese-remainder block | [md](hodge-fermat-campaign/THE_LOCALIZATION_THEOREM.md) |
| **The Block Decomposition** | the splitting of the group ring over $\mathbb{F}_p$ into blocks — the precedent of the colour reduction of §6 | [md](hodge-fermat-campaign/THE_BLOCK_DECOMPOSITION.md) · [pdf](hodge-fermat-campaign/THE_BLOCK_DECOMPOSITION_EIGENCUT_v2.pdf) |
| **The Nail Theorem** | the rank of every block is the Degtyarev–Shimada value, unconditionally | [md](hodge-fermat-campaign/THE_NAIL_THEOREM.md) · [pdf](hodge-fermat-campaign/THE_NAIL_THEOREM_CLOSED_EIGENCUT.pdf) |
| **Sixteen verdicts** | sixteen cells decided by machine, eleven beyond the published table — explicitly *not* a theorem | [md](hodge-fermat-campaign/SIXTEEN_VERDICTS.md) |
| The Sweet Lie, the Bend, the Wild Tooth, the Three-Ring, the Within-Pair Functor | further laws of the same lattices | see the [campaign README](hodge-fermat-campaign/README.md) |

## 6. Statements in the record that are false — do not build on them

The archive keeps every retracted statement under the line that retracts it. These are the ones most likely to mislead:

| Statement | Why it is false | Where |
|---|---|---|
| «Conjecture 1.2 ⟺ $A_k(q) = P_k(q)$» | the count of Theorem A is a sum statement at the odd box $q$; the conjecture is an intersection statement at the even box $q-1$; for subfamilies the two are independent | paper §1.8, §9; [record/audits/the-23-september-retraction.md](record/audits/the-23-september-retraction.md) |
| the *Descent Principle* (the hypothesis at $q=3$ implies it at every $q = 3^v$) | its Lemma B is false (counterexample $t = e_1$); the Sofa campaign itself retracted it on 3 July 2026 | the [Cemetery](archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) |
| the *Orbit Criterion*, and every hereditary criterion for the defect | fourteen of the fifteen sheets of $k=2$ already have defect $1$ | the Cemetery (tombs T-19, T-20) |
| the *invariant-defect law* ($A_F(q) - P_F(q)$ independent of $q$) | five hyperplanes of $\mathbb{A}^4$ over $\mathbb{F}_3$ give $6$ at $q=3$ and $18$ at $q=9$ | the Cemetery |
| every «tower lift» from $q$ to $3q$ strong enough to close the conjecture | any such bound is equivalent to the step it wants to prove | the Cemetery |

For the complete list — more than three hundred dead routes, each with the reason it failed — read the [Cemetery](archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) (in Spanish).

---

[README](README.md) · [How to verify](HOW_TO_VERIFY.md) · [Where to attack](WHERE_TO_ATTACK.md) · [The story and the numbers](THE_STORY_AND_THE_NUMBERS.md)
