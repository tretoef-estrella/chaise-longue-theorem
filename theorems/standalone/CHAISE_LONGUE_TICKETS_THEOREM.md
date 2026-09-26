> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-18
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE TICKETS THEOREM · v2 (depth m > 0: the surjective half of the Anchor Law, at every depth, threshold q ≥ 2(k+m)+1)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_TICKETS_THEOREM.md
>
> **Status, as written in the document:** Standalone theorem · 18 Jul 2026 · Constructor: Fresh Eyes (Fable) · Mission assigned by Vernier (m > 0, the load-bearing unlocked piece), handle supplied by Vernier (the deficit inequality), mechanism completed here · PASSED by Vernier (pencil, full), with on…
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (6 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v2`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE TICKETS THEOREM · v2 (depth m > 0: the surjective half of the Anchor Law, at every depth, threshold **q ≥ 2(k+m)+1**)
### Standalone theorem · 18 Jul 2026 · Constructor: Fresh Eyes (Fable) · Mission assigned by Vernier (m > 0, the load-bearing unlocked piece), handle supplied by Vernier (the deficit inequality), mechanism completed here · **PASSED by Vernier (pencil, full), with one repair applied in v2** · Load-bearing — audit surface §5 · Pending P0.

**Builds on:** Vernier's deficit reading (restriction to V_J is ∏(−1)^{α_{b_p}} w_p^{s_p}, s_p = α_{a_p}+α_{b_p}, surviving iff every s_p ≤ q−1 — an *inequality*, whose rigidity at m=0 was a gift of the degree); ISOLATION (the m=0 case, recovered verbatim); the box structure B_J = F₃[w]/(w^q).

---

## 1. Theorem TICKETS

> **Theorem.** Let k ≥ 1, m ≥ 0, and q = 3^v with **q ≥ 2(k+m)+1**. Then Φ_{top−m} : A_{(k+1)(q−1)−m} → ⊕_J (B_J)_{top−m} is **surjective**; hence
> **A_{(k+1)(q−1)−m}(k,q) ≥ (2k+1)!!·C(m+k, k).**
> At m = 0 the threshold is 2k+1 and the construction degenerates to Isolation exactly.

*Proof.* A basis vector of ⊕_J(B_J)_{top−m} is a pair (J, t): a sheet and a **deficit distribution** t = (t_p) with t_p ≥ 0, Σt_p = m (the slot ∏ w_p^{q−1−t_p}); there are C(m+k,k) slots per sheet — the Anchor Law's count, now with a meaning: **m tickets distributed among k+1 pairs.** For each target (J,t) build one monomial:

**(a) Sorted adaptive colours.** Order the pairs of J by ticket, ascending; assign c_{(1)} = 0 and c_{(i+1)} = c_{(i)} + t_{(i)} + 1. Then the values c_p + t_p are strictly increasing along the order, and the largest satisfies c + t ≤ m + k. Set α = c_p on one endpoint and q−1−c_p−t_p on the other, for each pair p of J. Well-defined (large > small) because q−1 > 2c_p + t_p, guaranteed by q−1 ≥ 2(m+k).

**(b) The ≤-graph has a unique perfect matching.** Write d_p := c_p + t_p; by (a) the d_p are **strictly increasing** along the sorted order, hence pairwise distinct, with values in [0, m+k]. A sheet J′ sees x^α iff every J′-pair sum is ≤ q−1: the survivors are the perfect matchings of Γ_≤(α).
> *Large–large edges are absent, strictly, even on the threshold boundary.* The two largest large-values are q−1−d and q−1−d′ with d ≠ d′ both ≤ m+k, so d + d′ ≤ 2(m+k) − 1, and their sum is ≥ 2(q−1) − (2(m+k) − 1) > q−1 whenever q−1 ≥ 2(m+k). **The strict inequality comes from the distinctness of the d_p, not from slack in q** — which is why the boundary cell q−1 = 2(k+m) (e.g. (3,9,m=1)) is covered. *(This replaces v1's line "large–large sums are ≥ 2(q−1) − 2(m+k) > q−1", which degenerates to ≥ at exactly that boundary — Vernier's repair; strict monotonicity carries both the non-edges and the uniqueness.)*

So any perfect matching sends all k+1 large vertices to small ones, exhausting both sides; small–small edges, though present, are unusable. Large_p ~ small_{p′} iff c_{p′} ≤ d_p; strict monotonicity of d makes this a **strict staircase**, whose unique perfect matching is forced from the bottom: the diagonal — i.e. **J itself**, with pair sums s_p = q−1−t_p. The image is ±(the target slot), and no other sheet sees the monomial. ∎

**(c) Why m = 0 was rigid, and why the rigid recipe stalled at 175/420 (the diagnosis Vernier asked for).** At m = 0 the total degree (k+1)(q−1) forces every inequality s_p ≤ q−1 into equality — the rigidity was a gift of the degree, not a hypothesis. At m > 0 the slack is exactly m, and the rigid recipe realized **one** ticket pattern instead of all C(m+k,k): it was missing columns, not ideas — precisely as Vernier predicted. The adaptive sorted colours restore every column, and the previously stuck cell **closes: (3,9,m=1) = 420/420**.

## 2. Gates (all fresh, exhaustive per cell)

| cell | slots × sheets | isolating | verdict |
|---|---|---|---|
| (2,9,m=1) | 45 | **45/45** | FULL (Vernier's 45/45 recovered) |
| (2,9,m=2) | 90 | **90/90** | FULL |
| **(3,9,m=1)** | 420 | **420/420** | **FULL — the stuck cell closes** |
| (3,27,m=1..3) | 420/1050/2100 | all FULL | window covered |
| **(4,27,m=1..4)** | up to **66150** | **66150/66150** | **the entire k=4 anchor window at the campaign's M2 level** |
| (3,9,m=2), (3,9,m=3) | 1050, 2100 | 0 — construction infeasible | consistent: q=9 < 2(k+m)+1 = 11, 13 |

Threshold sharpness at the boundary: (3,9,m=1): 2(k+m)+1 = 9 = q, FULL; (3,9,m=2): 11 > 9, empty. The failures are all-or-nothing per distribution — the colour budget, not the combinatorics.

## 3. Consequence for the chain

With TICKETS, the **surjective half of the Anchor Law is a theorem at every depth m for q ≥ 2(k+m)+1** — over the whole anchor window m ≤ k, a **linear** threshold q ≥ 4k+1, where the retracted v1 chain assumed a quadratic gear. Composed with the mirror (FD-M): **ᾱ_{k(k+1)+m} ≥ (2k+1)!!·C(m+k,k)** in the same range. What remains for the full Anchor Law: the **ceiling half** (≤, the injectivity of Φ on those degrees) — the corpus files its mechanism as swap-product divisibility; tracing it is the next front — and the band q < 2(k+m)+1 (a dominoes-at-depth enlargement is the named seed to lower it, as DOMINO lowered ISOLATION).

## 4. Certificado de Cementerio (Ley 41)
Object: *depth-m monomials with adaptive ticketed colours isolating one (sheet, deficit-slot) pair via the strict staircase of Γ_≤.* No tomb; nearest neighbours ISOLATION (its m=0 case, recovered), DOMINO (different mechanism: two-sheet combinations below threshold), the "casa del gancho" layer decomposition (same inequality, different use — cited, not re-walked). CLEAN.

## 5. Audit surface (Vernier — the handle was yours; the staircase is mine to defend)
(A) The strict monotonicity of d_p = c_p+t_p under sorted assignment (**carries uniqueness AND the large–large non-edges — Vernier's repair, applied in v2**). (B) The boundary cell (3,9,m=1), q−1 = 2(k+m) exactly, re-derived by hand. (C) The all-or-nothing failure pattern at (3,9,m≥2) with independent code. (D) The sign bookkeeping of the slot hit. (E) Whether sorting is optimal — a smarter assignment might shave the threshold below 2(k+m)+1; named as quality, not validity.

**MARCADOR: [MISIÓN m>0 — LA MITAD SOBREYECTIVA DE LA ANCHOR LAW CERRADA A TODA PROFUNDIDAD: THEOREM TICKETS — los C(m+k,k) slots SON los repartos de m tickets entre k+1 pares (el handle de Vernier), y los colores adaptativos ORDENADOS los aíslan todos vía la escalera estricta de Γ_≤ ⟹ Φ_{top−m} sobreyectiva para q ≥ 2(k+m)+1 (lineal; m=0 ⟹ el 2k+1 de Isolation exacto) · la celda atascada CIERRA: (3,9,m=1) = 420/420; la ventana entera de k=4 a q=27 = 66150/66150 · el diagnóstico del 175 confirmado: faltaban columnas, no ideas · abierto declarado: la mitad techo (divisibilidad por el producto de swaps, siguiente frente), la banda q < 2(k+m)+1 (semilla dominó-en-profundidad), y la composición vía FD-M (P0-8, la deuda)]. — Fresh Eyes (Constructor)**
