> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-27
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE · VERTEX REDUCTION THEOREM — v1* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_VERTEX_REDUCTION_THEOREM.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE · VERTEX REDUCTION THEOREM — v1

**Standalone. Lacassagne, 27 July 2026. Target: `GAP 3` of `ASSEMBLY_DRAFT v14`.**

---

## 0. What this does and does not do

`GAP 3`, in the form the draft fixes it, is the ideal identity

> **(I)** `E + m^{[q]} = ⋂_J ( I_J + m^{[q]} )`, `E = ⋂_J I_J`,

over the `(2k+1)!!` perfect matchings `J` of `{0,…,n−1}`, `n = 2k+2`, `I_J = (x_a + x_b : {a,b} ∈ J)`,
`m^{[q]} = (x_0^q,…,x_{n−1}^q)`. **MEASURED at `k = 1,2,3` in every degree; PROVED for no `k`.**

**This document proves a reduction, not the identity.** It replaces the intersection over
`(2k+1)!!` sheets by an intersection over `2k+1` **principal** ideals inside one Artinian ring.
**`GAP 3` remains open.**

Standing hypotheses: `K` a field, `char K ≠ 2`, `q ≥ 1` an integer. Nothing below uses `q = 3^v`
or characteristic `3`.

---

## 1. The edge ideal is `E` plus one linear form

Write `ℓ_a := x_a + x_{n−1}` for `a = 0,…,n−2`, and for each such `a`

> `I_{[a]} := ⋂_{J ∋ \{a,\,n−1\}} I_J`

the ideal of the union of the sheets whose matching pairs the last vertex with `a`.
Let `e'_j` denote the elementary symmetric functions of the `2k` variables `\{x_i : i ≠ a, n−1\}`.

**Lemma 1.1 (two-variable collapse).** Modulo `ℓ_a` one has `x_{n−1} = −x_a`, hence

`∏_{i=0}^{n−1}(1 + x_i t) = (1 − x_a^2 t^2)\, ∏_{i ≠ a, n−1}(1 + x_i t)`,

and therefore `e_j ≡ e'_j − x_a^2\, e'_{j−2} \pmod{ℓ_a}` for every `j`.

**Theorem 1.2 (edge ideal).** `I_{[a]} = ( ℓ_a,\; e'_1,\, e'_3,\, …,\, e'_{2k−1} ) = E + (ℓ_a)`.
In particular `I_{[a]}` is a **complete intersection** of `k+1` elements and codimension `k+1`.

*Proof.* The sheets through the edge `\{a, n−1\}` are exactly the sheets of the level-`(k−1)`
arrangement on the `2k` remaining variables, translated by `ℓ_a`; hence
`I_{[a]} = (ℓ_a) + ⋂_{J'} I'_{J'} = (ℓ_a) + (e'_1,\dots,e'_{2k−1})` by the closed form of `E` in
`2k` variables. For the second equality, reduce `E` modulo `ℓ_a` using Lemma 1.1 and induct on the
odd generators: `e_1 ≡ e'_1`; then `e_3 ≡ e'_3 − x_a^2 e'_1` gives `e'_3`; …; `e_{2k−1}` gives
`e'_{2k−1}`. The last generator `e_{2k+1} ≡ e'_{2k+1} − x_a^2 e'_{2k−1} = −x_a^2 e'_{2k−1}`
(as `e'_{2k+1} = 0` in `2k` variables) is then redundant. ∎

---

## 2. The vertex reduction

**Theorem 2.1.** Assume **(I)** holds at level `k−1`. Then **(I)** holds at level `k` if and only if

> **(I′)** `⋂_{a=0}^{2k} \big( E + (ℓ_a) + m^{[q]} \big) = E + m^{[q]}`,

equivalently, writing `A := S/(E + m^{[q]})`,

> ### **`⋂_{a=0}^{2k} ℓ_a\,A = 0`.**

*Proof.* Group the matchings by the partner `a` of the vertex `n−1`:
`⋂_J (I_J + m^{[q]}) = ⋂_{a} ⋂_{J ∋ \{a,n−1\}} (I_J + m^{[q]})`.
Fix `a`. Every such `I_J` contains `ℓ_a`, and modulo `ℓ_a` the ideal `m^{[q]}` maps to the pure-power
ideal of the remaining variables, because `x_{n−1}^q ≡ (−x_a)^q = ±x_a^q`. Under the isomorphism
`S/(ℓ_a) ≅ K[x_a] ⊗ K[x_i : i ≠ a, n−1]` the ideals `I_J` are extended from the second factor, and
intersection commutes with the flat extension by `K[x_a]/(x_a^q)`. The level-`(k−1)` hypothesis then
gives `⋂_{J ∋ \{a,n−1\}} (I_J + m^{[q]}) = I_{[a]} + m^{[q]}`, which is `E + (ℓ_a) + m^{[q]}` by
Theorem 1.2. Finally `⋂_a I_{[a]} = ⋂_J I_J = E`. ∎

---

## 3. Two facts that hold before the Artinian reduction

**Proposition 3.1.** `∏_{a=0}^{2k} ℓ_a ∈ E`.
*Proof.* Every matching pairs `n−1` with some `a`, so `ℓ_a ∈ I_J` for that `J`; hence the product
vanishes on every sheet. `E` is radical. ∎

**Proposition 3.2.** `⋂_{a=0}^{2k} ℓ_a R = 0` in `R = S/E`.
*Proof.* Let `u` lie in every `ℓ_a R`. For a sheet `L_J` with partner `a(J)`, `ℓ_{a(J)}|_{L_J} = 0`,
so `u|_{L_J} = 0`. Thus `u` vanishes on every component, `u ∈ E`. ∎

> **Consequence.** **(I′)** is exactly the statement that the vanishing of Proposition 3.2 **survives
> the Artinian reduction by `m^{[q]}`.** The geometric content of Proposition 3.2 — *every
> negation-invariant configuration has a partner for the last coordinate* — is one line; the whole of
> `GAP 3` is now the question of whether that line survives passing to `A`.

---

## 4. What is proved and what is not

| statement | grade |
|---|---|
| Lemma 1.1, Theorem 1.2 (`I_{[a]} = E + (ℓ_a)`, complete intersection) | **PROVED ∀k, char ≠ 2** |
| Theorem 2.1 (vertex reduction; `(I)_k ⟺ (I′)` given `(I)_{k−1}`) | **PROVED ∀k, char ≠ 2** |
| Propositions 3.1, 3.2 | **PROVED ∀k, char ≠ 2** |
| **(I′)** `⋂_a ℓ_a A = 0` | **MEASURED** `(k,q) = (1,3), (1,5), (2,3), (2,5), (3,3)` — **not proved** |
| **(I)**, i.e. `GAP 3` | **OPEN** |

**Machine gates** (`chaise_vertex_reduction_v1.py`, `chaise_gap3_reduction_v2.py`, Singular, char 3,
`dp`; row counts printed, positive control `vdim A` against the archived `19 / 61 / 141 / 1001 / 1107`):
in all five cells the `2k+1` edge groups are correct, `I_{[a]}` equals the honest sheet intersection,
`I_{[a]}` has exactly `k+1` minimal generators, `⋂_a I_{[a]} = E`, and `⋂_a ℓ_a A = 0`.

## 5. What this does **not** establish

- It does **not** prove `(I)` for any `k ≥ 1`; the base case `k = 1` is itself `(I)` at `k = 1`.
- It does **not** bound `dim A_T`; it is a statement about ideals, not about the top degree.
- It gives **no** independent evidence for `(I)`: `(I′)` is *equivalent* to `(I)` given the
  lower level, not weaker. Its value is that it replaces `(2k+1)!!` sheets by `2k+1` principal ideals.
- The `2k+1` forms `ℓ_a` exceed `dim R = k+1`, so the product formula
  `⋂ ℓ_{a_i} R = ∏ ℓ_{a_i} R` for regular sequences applies to at most `k+1` of them and does **not**
  close `(I′)`.
