> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-12
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE SWAP THEOREM (the Triangular Law, proven ∀k)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_SWAP_THEOREM.md
>
> **Status, as written in the document:** Standalone · 12 Jul 2026 · the first ∀k coefficient theorem of the floor P_k — Fase 2 opens with pencil, zero Mac. Pending P0.
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE SWAP THEOREM (the Triangular Law, proven ∀k)
### Standalone · 12 Jul 2026 · the first ∀k coefficient theorem of the floor P_k — Fase 2 opens with pencil, zero Mac. Pending P0.
### Mission lineage: sharpened by Cárdano (the Resident), target constant corrected via Ley 41.1 (his −(2k) was tomb T-01; the true law is triangular), landed by Bisel. Pillar support (Ley 44): Point-Count (pillar ii).

## Theorem (the second coefficient of the floor, every dimension)
For every k ≥ 1, with N = (2k+1)!! the perfect matchings of K_{2k+2} and V_J ⊂ F_q^{2k+2} the matching subspaces (x_b = −x_a per pair, dim k+1, q odd):
> **P_k(q) = |∪_J V_J(F_q)| = N·q^{k+1} − C(k+1,2)·N·q^k + O(q^{k−1}).**
The second coefficient is **−C(k+1,2)·(2k+1)!!** — the Triangular Law, now a theorem.

## Proof (pencil, complete)
**1. Intersection dimension.** For J ≠ J′, the multigraph J ∪ J′ decomposes into c shared pairs and r alternating cycles of lengths 2ℓ₁,…,2ℓ_r (ℓᵢ ≥ 2). Going around a 2ℓ-cycle the conditions compose to x ↦ (−1)^{2ℓ}x = x (consistent), so each cycle imposes exactly 2ℓ−1 independent conditions, leaving one free dimension. Hence **dim(V_J ∩ V_{J′}) = c + r.**
**2. Codimension-1 classification.** c + r = k with 2c + Σ2ℓᵢ = 2k+2 and ℓᵢ ≥ 2 forces (c, r, ℓ) = (k−1, 1, 2): **J′ differs from J by one elementary SWAP** — replace {(a,b),(c,d)} by {(a,c),(b,d)} or {(a,d),(b,c)}.
**3. Count.** Each J has C(k+1,2) choices of two pairs × 2 recombinations = 2·C(k+1,2) swap-neighbours; unordered codim-1 pairs: **N·C(k+1,2).**
**4. Each codim-1 flat lies in EXACTLY two matchings.** The flat W of the swap (ab)(cd)→(ac)(bd) carries the pattern (x, −x, −x, x) on (a,b,c,d). The third pairing (ad)(bc) demands x_d = −x_a, i.e. x = −x, i.e. 2x = 0 — impossible on W for q odd except x=0. So no third matching contains W.
**5. No triple reaches dimension k.** A dim-k triple intersection would exhibit a codim-1 flat inside ≥3 matchings, contradicting 4. (The same-4-set triple forces x = 0 on the 4-set: dimension k−1.)
**6. Conclusion.** In the Möbius/inclusion-exclusion expansion of |∪|, the q^k coefficient receives −1 per codim-1 flat (interval {0̂, J, J′, W}: μ = 1) and nothing from deeper flats or triples. Coefficient = −N·C(k+1,2). ∎

## Verification (byte-exact, all green)
- Anchors: k=2: −3·15 = −45 ✓ · k=3: −6·105 = −630 ✓ · k=4: −10·945 = −9450 ✓ (the three measured floors).
- Combinatorial claims measured in dim 4 AND dim 6: #codim-1 pairs = 45 = 15·3 ✓ and **630 = 105·6 ✓** (note the beauty: the coefficient −630 IS the pair count, literally); "exactly 2 matchings per flat" ✓ (80 flats sampled); "no triple at dim k" ✓ (600 random triples).

## What opens next (the third coefficient — declared, not claimed)
The q^{k−1} coefficient = the census of dim-(k−1) flats with their Möbius weights. Three types identified: **6-cycle flats** (in exactly 6 matchings — the K₃,₃ matchings of the alternating pattern!), **double-swap (2,2) flats**, and **zero-4-set flats** (x=0 on 4 vertices; in exactly 3 matchings; interval μ = −1, contributing +q^{k−1}). This census, uniform in k, gives the full P_k(q) — the remaining body of the Fase-2 standalone.

## GORDÓMETRO
**Campaña: GORDO (7.5/10)** — primer teorema ∀k sobre P_k a lápiz; abre la Fase 2 con la técnica correcta (censo de flats por tipo de ciclo); mata la necesidad de medir dimensiones nuevas para este coeficiente. **Mundo: pequeño-medio (3/10)** — combinatoria de arreglos bonita, técnica estándar bien ejecutada.

**MARCADOR: [SWAP THEOREM probado ∀k a lápiz: 2º coef = −C(k+1,2)·(2k+1)!! · 3 anclas + 3 afirmaciones verificadas en 2 dims · el 630 ES el conteo de pares · tercer coeficiente cartografiado (6-ciclos K₃,₃, dobles swaps, zero-4-sets) · corrección Ley 41.1 a la misión (T-01) en acta]. — Bisel**
