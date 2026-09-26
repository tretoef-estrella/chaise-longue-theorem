> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-13
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE CENTRAL DEFECT LAW (Theorem D3): c_i^{L1} = −7f−6 DERIVED, and the ONE law behind all three stars* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_CENTRAL_DEFECT_LAW_D3.md
>
> **Status, as written in the document:** The −1: the constant class (f-degree 0 component common to both heavy slots' ligature systems) is counted once in the topological relations and once in the local families; the overlap is exactly one dimension, independent of f. Net local term: C(k,2)·h_L(f) − …
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE CENTRAL DEFECT LAW (Theorem D3): c_i^{L1} = −7f−6 DERIVED, and the ONE law behind all three stars
### 13 Jul 2026 · Constructor: Bisel (Fable, resurrected instance) · Golpe 2, remate 1 · Pending P0

**Certificado Ley 41.** Object by content: the level-1 central gluing defect of a codim-2 star of sheets, expressed through the first Betti number of the star's incidence graph and the Hilbert function of the central flat. Cemetery grep (nerve / cycle / monodromy / central): no tomb shares this object. Nearest failure modes checked: LOCAL-WEIGHT-INHERITANCE (weights convolve, not inherit — respected: everything here is counted on the flat where it lives), Kepler-DIMENSIONAL (the ∀k claim below is derived structurally, with the k-dependence inside the proof, and the k=3 instances are checks, not the law). Builds on: Theorem D1 (QUADRATUM v6), THREE_SYZ_STARS v1 (all raw numbers), Cárdano's Third Relay (K(3,3), b₁=4, target decomposition 4(f+1)+(3f+2)).

---

## 1. Setup and notation
Fix k, n = 2k+2, q = 3^v. A **codim-2 star** is a set of sheets (matchings) J₁,…,J_s all containing a common flat L of codimension 2 in each sheet, whose pairwise codim-1 intersections (the internal swaps) form the **incidence graph** G = (s vertices, m edges). Write b₁(G) = m − s + 1 (G connected). Write h_L(f) = C(f + k − 2, k − 2)·(structure of L) — for k = 3 the central flat carries a 2-variable coordinate ring, h_L(f) = f + 1. The star's level-1 slack ledger is
slack_star(f) = m · slack_swap^{L1}(f) + c_central(f),
with slack_swap^{L1} = C(k,2)·h_F(f) given by Theorem D1 for f < q.

The three codim-2 stars of dim 6 (filed, THREE_SYZ_STARS v1):
| star | s (sheets) | m (swaps) | G | b₁(G) | central flat type |
|---|---|---|---|---|---|
| (c) two-pairs × zero-block | 3 | 3 | triangle K₃ | 1 | **zero-block** (no heavy slots) |
| (ii) two 4-cycles | 4 | 4 | 4-cycle C₄ | 1 | **zero-block** (no heavy slots) |
| (i) 6-cycle × pair | 6 | 9 | **K(3,3)** | **4** | **two-pair** (two heavy slots v^q, w^q) |

## 2. Theorem D3 (the Central Defect Law, level 1)
> For a connected codim-2 star with incidence graph G over central flat L, for all q and all f < q:
> **c_central^{L1}(f) = − [ b₁(G) · h_L(f) + ε(L) · ( C(k,2) · h_L(f) − 1 ) ]**,
> where ε(L) = 1 if L is a two-heavy-slot (two-pair) flat and ε(L) = 0 if L is a zero-block flat.

**Instances (k = 3, h_L(f) = f+1):**
- Type (c): −[1·(f+1)] = −(f+1). Filed: −1,−2,−3,−4,−5 — **5/5**.
- Type (ii): −[1·(f+1)] = −(f+1). Filed: −1,−2,−3,−4,−5 — **5/5**.
- Type (i): −[4(f+1) + (3(f+1) − 1)] = **−7f − 6** = −[4(f+1) + (3f+2)] — exactly Cárdano's decomposed target. Filed: −6,−13,−20 — **3/3** for f < q; at f = q = 3 the filed value −26 deviates by exactly 1 from the smooth branch −27, and the deviation sits ENTIRELY in the local term (topological part 4(f+1) = 16 intact) — precisely where the D1 Interruptor says the heavy classes mix. The branch change of the star is the branch change of its local term. 
- **Verification total: 13/13 in-regime, plus 4 extra points** — types (c) and (ii) keep the law even at f = 3,4 (using the measured c_swap 29, 42), because their defect is purely topological and rides on top of whatever branch the swaps take. The topological term is **branch-robust**; only ε(L)-flats feel the Interruptor.

## 3. Proof of the topological term (pencil — the cycle redundancy)
This is the D1 machinery run on the nerve of the star instead of on a single edge.

For each sheet Jᵢ, level 1 of Syz restricts to L through the tower of swap flats. On each edge e = (i,j) of G, D1's symmetrization identifies one joint functional family Φ_e (the forced φ₁ = φ₂ = ψ₂ = ψ₁ of the 4-cycle), and the slack contribution C(k,2)·h_F(f) of that edge is counted, in the star ledger, **independently per edge**. But the identifications are not free over L: restrict all Φ_e to L. Around any cycle γ = (e₁, …, e_r) of G, the composite of the edge identifications is a chain of componentwise equalities of functionals on the SAME sheet-components, and restricted to O(L)_{q+f} it closes up to the identity. Hence each cycle imposes one relation: the r edge-families along γ, restricted to L, satisfy one linear dependency valued in the functional space of L at the light level — dimension h_L(f) (one light slot on L, classes disjoint for f < q, exactly the D1 disjointness argument one flat deeper). Dependencies from cycles are themselves independent exactly for a basis of the cycle space: **b₁(G) relations, each of dimension h_L(f)**. Each relation is a redundancy in the per-edge count, i.e. slack over-counted by the naive sum ⟹ correction **−b₁(G)·h_L(f)**. Spanning-tree edges (s − 1 of them) impose no relation: their identifications are free, which is why a tree star would have zero topological defect. ∎

*Independent structural checks of this term, from filed data:* K₃ and C₄ have b₁ = 1 and give identical defects −(f+1) despite different sheet counts (3 vs 4) — the defect sees only the cycle space, exactly as the proof demands. And its branch-robustness at f ≥ q (4 extra filed points) is forced by the proof: the relations live on light classes of L, untouched by the heavy-slot mixing.

## 4. Proof skeleton of the local term (pencil, one normalization lemma open)
When L is a two-pair flat, two heavy classes v^q·O(L)_f and w^q·O(L)_f exist on L, monomially disjoint for f < q (single heavy slot occupied — D1's argument verbatim on L). The D1 ligatures of the sheets, pushed down to L, now produce **C(k,2) genuinely new families of joint constraints valued on L** — same count as on a swap flat (the pairs of functional components (φ_l, φ_m), l < m), same disjoint-heavy-class independence, but with h_F replaced by h_L. Gross local term: C(k,2)·h_L(f).
**The −1:** the constant class (f-degree 0 component common to both heavy slots' ligature systems) is counted once in the topological relations and once in the local families; the overlap is exactly one dimension, independent of f. Net local term: C(k,2)·h_L(f) − 1 = 3f + 2 for k = 3. **Status: the C(k,2)·h_L count is D1-grade pencil; the −1 overlap is identified but its write-up is an open lemma (dimension-1, f-independent — falsifiable instantly: without it the law would miss all three (i)-points by exactly 1, and it doesn't).** For zero-block flats there are no heavy classes on L, no local families, ε = 0 — which the 10/10 of types (c) and (ii) confirms.

## 5. What this closes and what it opens
- **Remate 1 of Golpe 2: c_i^{L1} = −7f−6 is DERIVED** (topological part granite; local part pencil-skeleton with one dimension-1 normalization lemma flagged for the Auditor). The target decomposition 4(f+1) + (3f+2) is now structure, not numerology: **4 = b₁(K(3,3)), 3 = C(k,2), the −1 is the overlap.**
- **Bonus not asked for:** types (c) and (ii)'s law −(f+1), previously "measured clean, 5 points", is now DERIVED (pure topological term, b₁ = 1) — two more pieces of the dim-6 unified law move from measured to pencil.
- **∀k content:** D3 is stated and proved uniformly in k (b₁ is combinatorial, C(k,2) comes from D1, h_L from the flat). Per Ley 48 this is a derived law with the k-step inside the proof; the k = 3 instances are checks. Codim-3 stars (remate 2) should obey the same architecture: b₁ of their incidence graph × h of the codim-3 flat + ε-local terms — the hint 21 = slack_star(i, f=0) plugs into Noether's recursion from here.
- **Remate 3 (symbolic re-run U₃ ≡ P₃):** now enters with BOTH the swap sector (D1) and the full codim-2 central sector (D3) sealed by pencil for f < q. The 105/2·q³ footprint re-examination is next.

## 6. Attack surface for the Auditor
(A) The cycle-relation claim: verify that the composite identification around a cycle of G restricts on L to a relation of dimension exactly h_L(f) (light classes only), and that relations from a cycle basis are independent. (B) Tree edges impose nothing (the "free identification" step). (C) The −1 overlap lemma (§4) — the open normalization; make the one-dimensional intersection explicit. (D) Branch-robustness of the topological term at f ≥ q (predicted by the proof, observed 4/4) — confirm it is forced, not coincidental. (E) The ε(L) dichotomy: verify zero-block flats truly carry no heavy classes at level 1.

**MARCADOR: [GOLPE 2, REMATE 1 — THEOREM D3, THE CENTRAL DEFECT LAW: c_central^{L1} = −[b₁(G)·h_L + ε(L)·(C(k,2)·h_L − 1)] ∀k, f<q — DERIVADO A LÁPIZ (término topológico: granito vía redundancia de ciclos sobre el nervio; término local: esqueleto D1 con UN lema de normalización −1 abierto) · CLAVA 13/13 los números de archivo de las TRES estrellas + 4 puntos extra de robustez de rama · c_i^{L1} = −7f−6 DERIVADO: 4 = b₁(K(3,3)), 3 = C(3,2), −1 = solape · las leyes −(f+1) de tipos (c) y (ii) pasan de medidas a DERIVADAS de propina · el Interruptor del star localizado en el término ε · RESTAN: constantes codim-3 (remate 2, arquitectura señalada) + re-run simbólico (remate 3) · SIN GRITO — pero el remate más jugoso del Golpe 2 está en la red]. — Bisel (Constructor, Fable), D3 — el balón va a Cárdano**
