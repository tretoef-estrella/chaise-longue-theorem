> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-12
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE DEPTH-TWO CENSUS THEOREM (third coefficient of P_k, proven ∀k)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_DEPTH_TWO_CENSUS_THEOREM.md
>
> **Status, as written in the document:** |---|---|---|
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE DEPTH-TWO CENSUS THEOREM (third coefficient of P_k, proven ∀k)
### Standalone · 12 Jul 2026 · with the Swap Theorem, THREE coefficients of the floor are now closed uniformly in k. Pending P0.
### Method credit: the Architect's scrape-counting metaphor — you can't see the deep joints, but you count the scrapes they leave. A 630-scrape debugged the Möbius. Pillar (Ley 44): Point-Count (ii).

## Theorem (the q^{k−1} coefficient of the floor, every dimension)
For every k ≥ 2:
> **[q^{k−1}] P_k(q) = 4·A(k) + B(k) + C(k)**, where
> **A(k) = C(2k+2,6)·10·(2k−5)!!** (6-block flats), **B(k) = ½·C(2k+2,4)·C(2k−2,4)·9·(2k−7)!!** (double-swap flats), **C(k) = C(2k+2,4)·(2k−3)!!** (zero-4-set flats).
Anchors exact: k=2: 55 ✓ · k=3: 1645 ✓ · k=4: 42525 ✓. **Falsifiable prediction: k=5 (dim 10): +1,074,150.**

## Proof (pencil, complete)
**1. Classification of dim-(k−1) flats (complete).** A flat of the matching arrangement decomposes [2k+2] into components; every component is matched internally by each containing matching ⟹ all components have EVEN size; nonzero components carry one free parameter with a balanced ± bipartition (each matching pairs + to −); zero-blocks (from odd cycles in unions of ≥3 matchings, e.g. the K₄ of a 4-set) have even size ≥ 4. Dimension k−1 forces exactly: **(A)** one 6-block(3,3) + (k−2) pairs; **(B)** two 4-blocks(2,2) + (k−3) pairs; **(C)** one zero-4-block + (k−1) pairs. No other type exists (size accounting).
**2. Counts.** (A): 6-set × 10 balanced bipartitions × matching of the rest. (B): two disjoint 4-sets (unordered) × 3×3 bipartitions × rest. (C): 4-set × rest.
**3. Möbius weights (interval computations).**
- (A): atoms = the 3! = 6 K₃,₃-matchings of the block × fixed rest; intermediate = 9 codim-1 swap flats (transposition ratios); 3-cycle ratios land on W itself. μ = −(1 − 6 + 9) = **−4**.
- (B): atoms = 2×2; intermediate = 4 codim-1 flats (one block resolved); μ = −(1 − 4 + 4) = **−1**. *(First attempt used the naive product formula μ = +1; the k=3 anchor screamed 1645−1015 = 630 = the pair-count echo — the scrape that exposed the correct interval.)*
- (C): atoms = 3 matchings of the zero 4-set; intermediate = 3 swap flats; μ = −(1 − 3 + 3) = **−1**.
**4. Assembly.** |∪| = −Σ_{W≠0̂} μ(0̂,W)|W|; the q^{k−1} terms are exactly −μ·(count): 4A + B + C. ∎

## The state of the floor P_k(q), uniform in k
| coefficient | value | status |
|---|---|---|
| q^{k+1} | (2k+1)!! | PROVEN (atom count) |
| q^k | −C(k+1,2)·(2k+1)!! | PROVEN (Swap Theorem) |
| q^{k−1} | 4A(k)+B(k)+C(k) | **PROVEN (today)** |
| q^{k−2} and below | depth-3+ census | the machinery is set: classify even-balanced blocks + zero-blocks, interval Möbius, count. Mechanical descent. |

## GORDÓMETRO
**Campaña: GORDO (8/10)** — el método del censo por profundidad está ahora DEMOSTRADO como máquina que funciona (dos coeficientes seguidos cerrados ∀k); P_k completo es descenso mecánico; la Fase 2 tiene motor. **Mundo: pequeño-medio (3.5/10)** — combinatoria de arreglos sólida.

**MARCADOR: [DEPTH-TWO CENSUS probado ∀k: coef(q^{k−1}) = 4A+B+C · 3 anclas exactas (55/1645/42525) · predicción falsable dim10: 1.074.150 · la pupa-630 debugó el μ (método del Architect en acta) · P_k: 3 coeficientes uniformes cerrados, descenso mecánico declarado]. — Bisel**
