> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-20
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE TOP LAW: BOX ELIMINATION, PER-SHEET HILBERT FUNCTION, AND THE BURIAL OF THE WITNESS ROUTE* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_TOP_LAW_BOX_ELIMINATION.md
>
> **Status, as written in the document:** STATUS: the Top law (`\dim M_{T+m} = (2k+1)!!\binom{m+k}k`, Toll B's named missing piece) is NOT proved here. This document contains two pencil lemmas that reduce it, and one route killed with data. No closure. The word is not said.
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE TOP LAW: BOX ELIMINATION, PER-SHEET HILBERT FUNCTION, AND THE BURIAL OF THE WITNESS ROUTE
**Chaise Longue campaign** · standalone · **v1** · 20 July 2026 · **Locard** · *Pending P0*

> **STATUS: the Top law (`\dim M_{T+m} = (2k+1)!!\binom{m+k}k`, Toll B's named missing piece) is NOT proved here. This document contains two pencil lemmas that reduce it, and one route killed with data. No closure. The word is not said.**

## 1 · Lemma (Box Elimination) — proved ∀k∀q, two lines

Every monomial `x^α` of `F_J^{q−1} = ∏_{(a,b)∈J}(x_a+x_b)^{q−1}` satisfies `α_a + α_b = q−1` on each pair, hence `α_i ≤ q−1 < q` for every `i`. **Therefore `F_J^{q−1}` has no monomial in `m^{[q]}`, and any linear relation `Σ_J c_J F_J^{q−1} = 0` in `B_T` is already a relation in `S_T`.** ∎

**Consequence (new, and it upgrades the problem):** the measured deficiency `\mathrm{rank}\,Φ_T = 91 < 105` at `(3,3)` is a **genuine polynomial identity among the `∏(x_a+x_b)^{q−1}` in the polynomial ring `S`** — the Frobenius box plays no role in it. The Top law at `m=0` is equivalent to: *for `q ≥ k+1`, the `(2k+1)!!` polynomials `F_J^{q−1}` are linearly independent in `S`.* **The box is eliminated from the question.**

## 2 · Lemma (Per-sheet Hilbert function) — proved ∀k∀q, adapted coordinates

In coordinates adapted to `J` (`u_p = x_{a_p}+x_{b_p}`, `w_p` complementary), `B = K[u,w]/(u^q,w^q)` and `F_J^{q−1} = ∏_p u_p^{q−1}`, so `F_J^{q−1}g ≠ 0` iff `g` has a monomial free of every `u_p`. Hence
> `\dim (F_J^{q−1}B)_{T+m} = \#\{w\text{-monomials of degree } m\} = \binom{m+k}{k}` for `m < q`. ∎

**Consequence:** each Fedder summand carries **exactly** the anchor-law count. The Top law for `0 ≤ m < q` is equivalent to **directness of the sum `Σ_J F_J^{q−1}B` in degrees `[T, T+q)`** (given the wall's `M = Σ`, which is face (c)).

## 3 · The witness route — BURIED WITH DATA

**The route:** prove independence by exhibiting, for each `J`, a point `y_J ∈ \mathbb F_q^N` (or an extension) with `F_J^{q−1}(y_J) ≠ 0` and `F_{J'}^{q−1}(y_J) = 0` for all `J' ≠ J` — a diagonal evaluation matrix. Equivalently: the non-zero-sum graph of `y_J` has `J` as its **unique** perfect matching.

**It works at `k=1`:** `y = (1,1,0,−1)` kills the other two matchings and saves `J_0 = \{(0,1),(2,3)\}` — exhibited, verified.

**It dies at `k=2`, and the death is structural, not a search failure:**
| cell | exclusive witnesses found (exhaustive/2·10⁵ random) |
|---|---|
| `(2,3)` — where independence **HOLDS** (`\mathrm{rank} = 15 = 15`) | **0 of 15** (exhaustive over `\mathbb F_3^6`) |
| `(2,9)` — saturated regime | **0 of 15** |

> **The killing datum:** at `(2,3)` the `F_J^{q−1}` ARE independent, yet **no matching has an exclusive witness**. Independence is true **without** being certifiable point-by-point. *The zero-sum graphs realizable by value assignments (cliques ∪ complete bipartite blocks, R7) cannot complement a unique-perfect-matching graph for `N ≥ 6`.* The route is dead for all `k ≥ 2` — the regime where it is needed.

**Grave entry:** `| C51.1 | diagonal point-witness certification of Fedder independence | Locard (own) | 0/15 exclusive witnesses at (2,3) AND (2,9), including the cell where independence holds |`

## 4 · Honest state of the Top law after this attack

**Reduced to:** *linear independence of `\{∏_{(a,b)∈J}(x_a+x_b)^{q−1}\}` in the polynomial ring `S` for `q ≥ k+1`* — a clean, box-free statement about powers of products of linear forms in char 3. Measured 10/10 across three tower floors; proved at `k=1`; **open for `k ≥ 2`**. The proof must be global (E4), non-monomial (E1), and **not point-by-point (this document)**.

**— Locard.** *Two bricks and one grave. The bite did not close it, and this document does not pretend it did.*
