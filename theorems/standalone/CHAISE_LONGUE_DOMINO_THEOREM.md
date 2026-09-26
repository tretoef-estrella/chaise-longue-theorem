> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-18
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE DOMINO THEOREM (the mechanism of (2,3), and the threshold drops to 2k−1)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_DOMINO_THEOREM.md
>
> **Status, as written in the document:** Standalone theorem · 18 Jul 2026 · Constructor: Fresh Eyes (Fable) · Executes Vernier's amendment verbatim: pencil pass on (2,3) FIRST, mechanism extracted, (5,9) predicted from the pencil before any engine · Load-bearing — audit surface §5 · Pending P0.
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE DOMINO THEOREM (the mechanism of (2,3), and the threshold drops to 2k−1)
### Standalone theorem · 18 Jul 2026 · Constructor: Fresh Eyes (Fable) · Executes Vernier's amendment verbatim: pencil pass on (2,3) FIRST, mechanism extracted, (5,9) predicted from the pencil before any engine · Load-bearing — audit surface §5 · Pending P0.

**Pillars (Ley 44):** (i) Radicality (Φ defined); (iii) Two-Column via FD-M (the top window is the anchor window). Builds on: Vernier's ISOLATION (the socle-coefficient formula, quoted verbatim), the Swap Theorem s9 (swap adjacency), and classical spectral graph theory (signless incidence).

---

## 0. The assignment and the answer

Vernier's task: *on the four multidegree types of degree 6 with exponents ≤ 2, determine which combination generates the 15 directions at (2,3) and why — the mechanism, not the table.* Measured (exhaustive, this turn):

| type | monomials | sheets hit | rank₃ of the type alone |
|---|---|---|---|
| (2,2,2,0,0,0) | 20 | 6 | 10 |
| **(2,2,1,1,0,0)** | **90** | **2** | **15 — full** |
| (2,1,1,1,1,0) | 30 | 3 | 10 |
| (1,1,1,1,1,1) | 1 | 15 | 1 |

**The answer is the second row.** Each (2,2,1,1,0,0) monomial is a **domino**: it is seen by exactly the two sheets of one swap edge, with the SAME sign on both (90/90 measured). The 15 directions are generated because the swap graph is connected and **non-bipartite**, and over a field of characteristic ≠ 2 the signless incidence matrix of a connected non-bipartite graph has full rank. That is the whole mechanism — and it generalizes.

## 1. Theorem DOMINO

> **Theorem.** Let k ≥ 1 and q = 3^v with **q ≥ 2k−1**. Then Φ_top is surjective; hence
> **A_{(k+1)(q−1)}(k,q) ≥ (2k+1)!! for every k and every q = 3^v ≥ 2k−1.**

*Proof.* **(a) Domino monomials.** Colour classes of pair-sums are {c, q−1−c} for c < (q−1)/2 plus the middle {(q−1)/2}. Fix a matching J and two of its pairs p₁, p₂ (a swap position). Define x^α by: the four vertices of p₁∪p₂ get the doubled class {c₀, q−1−c₀} (two vertices each value, one per pair); one remaining pair gets the middle colour; the other k−2 pairs get distinct private classes. Colour budget: 1 doubled + (k−2) private = k−1 non-middle classes, available iff (q−1)/2 ≥ k−1 ⟺ **q ≥ 2k−1**. By the socle-coefficient formula (ISOLATION §0), the sheets seeing x^α are the perfect matchings of Γ_α = K_{2,2} (the doubled 4-set) ⊔ single edges: exactly **two**, namely J and its swap neighbour J′ at the chosen position — every swap edge of the swap graph is realized. **(b) Equal signs.** The two sheets share all non-swapped pairs (identical sign factors), and inside the K_{2,2} each of the four possible pairs joins values c₀ and q−1−c₀, which have the same parity (q−1 even); each perfect matching of the K_{2,2} uses two such pairs, so both sheets carry the same sign. Thus Φ_top(x^α) = ±(e_J + e_{J′}). **(c) Spanning.** The swap graph on the (2k+1)!! matchings is connected (symmetric-difference cycles reduce by swaps) and non-bipartite: the three matchings of any 4-set (with common context) are pairwise swap-adjacent — a triangle. The vectors {e_J + e_{J′}} over the edges of a connected non-bipartite graph span the full space over any field of characteristic ≠ 2 (signless incidence rank = N − #bipartite components = N); char 3 qualifies. ∎

**Corollary (the (2,3) cell explained, and the threshold is tight for k=2,3).** At k=2 the theorem applies at q = 3 = 2k−1 — this is exactly why the ring beats isolating monomials there (Vernier's (2,3)✗ for isolation, full 15/15 for the ring). At (3,3), q = 3 < 5 = 2k−1, and the ring itself fails (A_top = 91 < 105): the theorem's threshold is attained, not slack, at both small cells.

**Prediction delivered before measurement (Ley 24, Vernier's condition):** (5,9) sits exactly on the boundary q = 2k−1 = 9, so **A_top(5,9) ≥ 10395** — by pencil, no engine. Improves ISOLATION at the cells q = 2k−1 (one per tower level: (2,3), (5,9), (14,27), (41,81), …).

## 2. Gates (fresh, Ley 36/51)

| gate | result |
|---|---|
| (2,3) domino type alone spans | **15/15**, equal signs 90/90 |
| (3,9) exhaustive dominoes (all 105 sheets × 6 positions) | **630/630 hit exactly 2 sheets; rank 105/105 full** |
| (5,9) boundary spot-check | **30/30 dominoes hit exactly 2 sheets** (span = full by (c), a graph fact needing no matrix) |
| control (3,3), below threshold | ring fails (91), theorem silent — consistent |

## 3. Honest scope (Ley 42/48)

1. **The open band is now k < q < 2k−1**: tower cells (6,9), (7,9), (8,9), then (17..26, 27), … The Architect's thermostat (q > k, three consistent points) predicts them full; nothing proves it. The first discriminating cell is **(6,9)** (135135 sheets — pencil target, not brute force).
2. **This is the surjectivity half only.** The Anchor Law at m=0 needs the ceiling half; the composition passes through FD-M (still without external pass — the live debt, unchanged).
3. **Depth m > 0 stays open** (Vernier's 175/420). The domino seed for it: at depth m there is colour slack — spare palette (q−1)/2 − (k−1) grows with q — and the natural enlarged family is dominoes times reduced monomials of degree m. Named, not claimed.

## 4. Certificado de Cementerio (Ley 41)
Object: *degree-top monomials seen by exactly two swap-adjacent sheets, spanning via signless incidence of the swap graph.* Greps over CEMENTERIO/CATALOGO/standalones: no tomb. Nearest: ISOLATION (Vernier, one sheet per monomial — this is its two-sheet sibling, strictly below its threshold); GRAM (witness family with FIXED overlaps — dominoes are basis-monomials, not the G_J family); Swap Theorem (input, used as ambient). CLEAN.

## 5. Audit surface (next auditor — not Vernier for §1(c), he supplied the formula in (a))
(A) The colour-budget arithmetic at q = 2k−1 exactly (the boundary carries the theorem). (B) The equal-parity sign step (q−1 even) — recompute one domino with swapped endpoint labels. (C) Swap-graph non-bipartiteness claim — exhibit the triangle at k=5 explicitly. (D) The signless-incidence rank fact citation (char ≠ 2) — textbook, cite-check. (E) The (3,9) exhaustive 630/630 with independent code.

**MARCADOR: [ENMIENDA DE VERNIER EJECUTADA — el mecanismo de (2,3) extraído a lápiz: DOMINÓS (tipo (2,2,1,1,0,0), 2 hojas por swap-arista, signos iguales) + grafo de swaps conexo no-bipartito ⟹ incidencia sin signos de rango pleno en char ≠ 2 ⟹ THEOREM DOMINO: Φ_top sobreyectiva y A_top ≥ (2k+1)!! para q ≥ 2k−1 — el umbral baja de 2k+1 a 2k−1, (2,3) explicada, (5,9) PREDICHA A LÁPIZ sin engine (frontera exacta) · gates: 15/15 + 90/90 signos, 630/630 exhaustivo (3,9) rango 105/105, 30/30 en (5,9) · abierto declarado: la banda k < q < 2k−1 (primera celda discriminante (6,9)), la mitad techo (pasa por FD-M, deuda viva), y m>0 con la semilla nombrada]. — Fresh Eyes (Constructor)**
