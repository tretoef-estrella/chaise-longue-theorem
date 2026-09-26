> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-26
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE DEFECT DEGREE THEOREM FOR THE MATCHING ARRANGEMENT* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_DEFECT_DEGREE_THEOREM.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (2 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE DEFECT DEGREE THEOREM FOR THE MATCHING ARRANGEMENT
## `deg C = (2k+1)!!·k(k+1)/2`, and the identification of its top support
### Chaise Longue campaign — standalone deposit v1
**Author:** Lacassagne (constructor) · **Commissioned by:** Orfila (auditor, mission #25) · **Architect:** Rafa · 26 Jul 2026

---

## ABSTRACT

Let `n = 2k+2`, `S = K[x_1,…,x_n]`, `char K ≠ 2`, let `L_J` be the `(2k+1)!!` sheets of the matching
arrangement and `E = ⋂_J I_J`. Define the **arrangement defect module** by the exact sequence

>   `0 ⟶ S/E ⟶ ⊕_J S/I_J ⟶ C ⟶ 0`.

This `C` is the module controlling `GAP 3` condition (I): (I) holds iff
`H_1(x^{[q]}; ⊕_J S/I_J) ↠ H_1(x^{[q]}; C)`.

> ### **THEOREM 1.** `dim C = k` and **`deg C = (2k+1)!!·k(k+1)/2`.**
> ### **THEOREM 2 (top support).** The top-dimensional support of `C` is indexed by the pairs of
> ### sheets meeting in dimension `k`, and **each sheet has exactly `k(k+1)` such neighbours** —
> ### the same `k(k+1)` as the swap hyperplanes of the `SINGULAR_LOCUS_LEMMA`, for the same reason.

Verified: `k=2` → `45`, `k=3` → `630`, and the bipartite subfamily `B_3` → `9`, each against an
independent combinatorial count of pairs.

> ### **⚠️ THEOREM 3 (scope separation, refutation).** This `C` is **NOT** the defect module `C(B_m)`
> ### of `MCM_REDUCTION_THEOREM_v2`. On the letter `B_3` both have `dim 2` and `deg 9`, but
> ### `HF = 5,13,22,31,40` here against the sealed `2,9,18,27,36`. **They are different modules.**
> ### No property of `C(B_m)` may be transported to this `C`. (`SCOPE-SPLICING` avoided by measurement.)

---

## 1 · THE DEGREE

**LEMMA 1.** For two distinct perfect matchings `J ≠ J'` of `[n]` sharing exactly `s` edges, the
union graph is `s` isolated edges together with even cycles covering the remaining `2(k+1−s)`
vertices. By the `STRATUM_CLASSIFICATION_THEOREM` every component is bipartite, so

>   `dim(L_J ∩ L_{J'}) = s + #cycles ≤ s + (k+1−s)/2 = (k+1+s)/2`,

and since `s ≤ k−1` for distinct matchings, `dim(L_J ∩ L_{J'}) ≤ k`, **with equality iff `s = k−1`
and the two remaining edges of each matching form a single 4-cycle.** ∎

**Call such a pair a PENCIL pair** (Sweet Lie vocabulary), and a pair attaining a strictly smaller
dimension a non-pencil pair.

**LEMMA 2 (neighbour count).** Fix `J`. To build a pencil partner, choose the `k−1` shared edges —
`\binom{k+1}{k-1} = \binom{k+1}{2}` ways — and rematch the four uncovered vertices into a 4-cycle,
`2` ways. Hence **every sheet has exactly**

>   `2\binom{k+1}{2} = k(k+1)`

**pencil neighbours**, and the total number of pencil pairs is `(2k+1)!!·k(k+1)/2`. ∎

**THEOREM 1.** `C` is supported on `⋃_{J≠J'}(L_J ∩ L_{J'})`, whose top-dimensional part is the union
of the pencil flats, each of dimension `k`; distinct pencil pairs give distinct flats. Hence
`dim C = k` and `deg C` is the number of pencil pairs:

>   **`deg C = (2k+1)!!·k(k+1)/2`.** ∎

| `k` | `(2k+1)!!` | `k(k+1)` | formula | counted independently | agree |
|---|---|---|---|---|---|
| 2 | 15 | 6 | **45** | 45 | yes |
| 3 | 105 | 12 | **630** | 630 | yes |
| 4 | 945 | 20 | 9450 | — | — |
| 5 | 10395 | 30 | 155925 | — | — |

The bipartite subfamily `B_3` (6 of the 15 sheets) gives `6·3/2 = 9`, also confirmed.

**Verification method.** `HF(C)_d = (2k+1)!!·\binom{d+k}{k} − \dim(S/E)_d`, with
`H(S/E) = (1−t)\prod_{i=2}^{k+1}(1−t^{2i−1})/(1−t)^{n}` from the complete-intersection structure of
`E` (degrees `1,3,…,2k+1`). Measured: `k=2` → `14,40,75,116,160,205,250`;
`k=3` → `104,413,1022,2017,3472,5447,7987`. Successive differences stabilise at `45` and `630`.
Reproducer: `defect_degree.py`.

---

## 2 · THE STRUCTURAL IDENTIFICATION (mission #25, asalto C)

The number `k(k+1)` of Lemma 2 is **the same integer** as the number of swap hyperplanes in the
`SINGULAR_LOCUS_LEMMA`, and this is not a numerical coincidence:

- The Singular Locus Lemma says `L_J ∩ ⋃_{J'≠J}L_{J'}` is the union of the `k(k+1)` swap hyperplanes
  `{u_p ± u_q = 0}` inside `L_J`, i.e. the `D_{k+1}` reflection arrangement.
- Lemma 2 says `L_J` has exactly `k(k+1)` neighbours meeting it in dimension `k`, i.e. in a
  hyperplane of `L_J`.
- **These are the same list.** The pencil partner obtained by swapping the pair of edges
  `\{a_p,b_p\},\{a_q,b_q\}` into `\{a_p,a_q\},\{b_p,b_q\}` cuts `L_J` exactly in `{u_p + u_q = 0}`;
  the other rematching gives `{u_p − u_q = 0}`. The two rematchings of Lemma 2 are precisely the two
  signs of the swap hyperplane.

> **Consequence.** The top-dimensional support of `C` is indexed by pairs *(sheet, swap hyperplane)*,
> i.e. by `\{(J,H) : H ∈ D_{k+1}(L_J)\}`, counted once per unordered pair. The defect module of the
> arrangement is assembled, at top dimension, out of exactly the data the Singular Locus Lemma
> classifies.

---

## 3 · SCOPE — WHAT THIS DOES *NOT* CLAIM

1. **It does not prove condition (I), nor `GAP 3`, nor any part of the surjectivity.** It computes
   an invariant of the module in which the obstruction lives.
2. **It does not compute `depth C`**, which was asalto B of mission #25 and is **not delivered**.
   Without it nothing follows about `H_1`.
3. **The identification of §2 is at the level of the indexing set and the top-dimensional support.**
   No claim is made that `C` decomposes as a sum over those pairs, nor that its lower-dimensional
   support (non-pencil pairs, dimension `< k`) is controlled.
4. `C` here is **not** `C(B_m)` of the MCM programme (Theorem 3 above). The `deg 9` coincidence on
   `B_3` is exactly the kind of match that `HILBERT-MATCH-IS-NOT-MODULE-MATCH` warns against: same
   `dim`, same `deg`, different Hilbert function.
5. `char K ≠ 2` is inherited from the `STRATUM_CLASSIFICATION_THEOREM`.
6. Verification is `k = 2, 3` plus the `B_3` subfamily; Theorems 1–2 are proved for all `k`.

---

## 4 · PROVENANCE

- The sequence `0→S/E→⊕S/I_J→C→0` and the reformulation of (I) as surjectivity on `H_1`: Orfila,
  mission #25.
- Pencil/skew vocabulary and the `45`/`60` pair census on `K_6`: `THE_SWEET_LIE_THEOREM`,
  independently recovered here as a by-product of Lemma 1.
- `k(k+1)` swap hyperplanes and the `D_{k+1}` identification: `SINGULAR_LOCUS_LEMMA_v1`, Lacassagne.
- Stratum dimensions: `STRATUM_CLASSIFICATION_THEOREM_v1`, Lacassagne.
- Lemmas 1–2, Theorems 1–3, the closed form and the verification: Lacassagne, this deposit.
- Route: the theorem was found while executing the death criterion of asalto A — comparing the two
  candidate `C`'s numerically instead of assuming they were the same object. The comparison
  separated them (Theorem 3) and, in doing so, produced the Hilbert function of the correct one,
  from which the degree law followed.

---

**Every statement carries its grade inline. The magic word is not spoken: `GAP 3` remains open.**
