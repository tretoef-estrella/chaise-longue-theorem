> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-23
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE SINGULAR LOCUS LEMMA FOR THE MATCHING ARRANGEMENT* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_SINGULAR_LOCUS_LEMMA.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (8 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE SINGULAR LOCUS LEMMA FOR THE MATCHING ARRANGEMENT
## Chaise Longue campaign — standalone deposit v1
**Author:** Lacassagne (constructor) · **Commissioned by:** Orfila (auditor) · **Architect:** Rafa · 23 Jul 2026

---

## ABSTRACT

Let `k ≥ 1`, let `N = 2k+2`, and let `S = K[x_1,…,x_N]` over a field `K` of characteristic `≠ 2`.
For each perfect matching `J` of `{1,…,N}` let

>   `L_J = { x_a + x_b = 0 : {a,b} ∈ J }`,

a linear subspace of dimension `k+1`. There are `(2k+1)!!` such sheets, and `⋃_J L_J` is the
matching arrangement of the campaign (Proposition 2.1 of the assembly draft).

**We prove, for every `k`, that the singular locus of the arrangement along a sheet is exactly the
reflection arrangement of type `D_{k+1}` inside that sheet:**

>   **`L_J ∩ ⋃_{J' ≠ J} L_{J'} = ⋃_{1 ≤ p < q ≤ k+1} ( {u_p + u_q = 0} ∪ {u_p − u_q = 0} )`,**

a union of **exactly `k(k+1)` distinct hyperplanes**, where `u_1,…,u_{k+1}` are the natural
coordinates on `L_J`. The proof is two paragraphs and uniform in `k`.

This was previously proved only for `k ≤ 3` (twelve hyperplanes at `k = 3`, by hand) and measured
at `k ≤ 4`. It is the input to the pinching of the annihilator that yields the **upper** bound of
the ceiling, and hence the finiteness of the verification window.

**What this lemma does NOT claim is stated in §4 and is essential to its correct use.**

---

## 1. NOTATION

Fix a perfect matching `J = {e_1,…,e_{k+1}}` of `{1,…,N}`, writing `e_p = {a_p, b_p}` with a chosen
order of the two endpoints. Parametrise `L_J` by

>   `x_{a_p} = u_p`,  `x_{b_p} = −u_p`  (`p = 1,…,k+1`),

which identifies `L_J ≅ A^{k+1}` with coordinates `u_1,…,u_{k+1}`. For a vertex `v ∈ {1,…,N}` let
`p(v)` be the index of the unique `J`-edge containing `v`, and set `ε(v) = +1` if `v = a_{p(v)}`,
`ε(v) = −1` if `v = b_{p(v)}`. Then

>   **(∗)  `x_v |_{L_J} = ε(v) · u_{p(v)}`.**

Call `H_{p,q}^{+} = {u_p + u_q = 0}` and `H_{p,q}^{-} = {u_p − u_q = 0}`, `1 ≤ p < q ≤ k+1`, the
**swap hyperplanes** of `L_J`.

---

## 2. THE LEMMA

**LEMMA (singular locus along a sheet, all `k`).** With the notation above, and `char K ≠ 2`,

>   `L_J ∩ ⋃_{J' ≠ J} L_{J'} = ⋃_{p<q} ( H_{p,q}^{+} ∪ H_{p,q}^{-} )`,

and the right-hand side consists of exactly `2·\binom{k+1}{2} = k(k+1)` pairwise distinct hyperplanes.

### Proof of `⊆`

Let `J' ≠ J` be any perfect matching and let `{c,d} ∈ J'`. Restricting its defining equation
`x_c + x_d = 0` to `L_J` and using `(∗)`:

>   `ε(c)·u_{p(c)} + ε(d)·u_{p(d)} = 0`.

Two cases, and only two:

- **`{c,d} ∈ J`.** Then `p(c) = p(d)` and `ε(c) = −ε(d)`, so the equation is `0 = 0`.
  *A common edge imposes no condition on `L_J`.*
- **`{c,d} ∉ J`.** Then `c` and `d` lie in different `J`-edges, so `p(c) ≠ p(d)`, and the equation
  reads `u_{p(c)} ± u_{p(d)} = 0` after dividing by `ε(c)`. *This is a swap hyperplane.*

Since `J' ≠ J`, at least one edge of `J'` is not an edge of `J`. Hence `L_J ∩ L_{J'}` is contained
in at least one swap hyperplane. Taking the union over all `J' ≠ J` gives `⊆`. ∎

### Proof of `⊇`

Fix `p < q`. Replace the two `J`-edges `e_p = {a_p,b_p}` and `e_q = {a_q,b_q}` by
`{a_p,a_q}` and `{b_p,b_q}`; all other edges are kept. The result is again a perfect matching
`J' ≠ J`, and by `(∗)` its two new equations restrict on `L_J` to `u_p + u_q = 0` (twice).
Hence `H_{p,q}^{+} ⊆ L_J ∩ L_{J'}`.

Replacing instead by `{a_p,b_q}` and `{b_p,a_q}` gives a matching `J'' ≠ J` whose new equations
restrict to `u_p − u_q = 0`, so `H_{p,q}^{-} ⊆ L_J ∩ L_{J''}`.

Every swap hyperplane is therefore attained. ∎

### The count

The linear forms `u_p + u_q` and `u_p − u_q` (`p < q`) are pairwise non-proportional as soon as
`2 ≠ 0` in `K`: two forms with the same support `{p,q}` differ by `2u_q`, and forms with different
supports are visibly independent. Hence the swap hyperplanes are `2·\binom{k+1}{2} = k(k+1)`
distinct hyperplanes, and they are precisely the reflection hyperplanes of the Weyl group of type
`D_{k+1}` acting on `A^{k+1}`. ∎

**Characteristic sensitivity.** In characteristic `2` the two forms coincide and the count collapses
to `\binom{k+1}{2}`. The campaign works over `F_3` and its tower `F_{3^v}`, so the hypothesis holds
throughout; but the statement is *not* characteristic-free and must not be quoted as such.

---

## 3. VERIFICATION

Independent machine check, `k = 1,…,5`: for the standard matching `J`, the set of hyperplanes
actually arising as `L_J ∩ L_{J'}` over **all** `(2k+1)!!` matchings `J' ≠ J` was computed and
compared with the `D_{k+1}` arrangement.

| `k` | `#` matchings | `dim L_J` | hyperplanes obtained | `k(k+1)` | equals `D_{k+1}` |
|---|---|---|---|---|---|
| 1 | 3 | 2 | 2 | 2 | yes |
| 2 | 15 | 3 | 6 | 6 | yes |
| 3 | 105 | 4 | 12 | 12 | yes |
| 4 | 945 | 5 | 20 | 20 | yes |
| 5 | 10395 | 6 | 30 | 30 | yes |

The `k = 3` row reproduces the twelve hyperplanes that were previously established by hand, and
`k = 4, 5` extend the previous measured range. Reproducer: `singloc.py`.

---

## 4. SCOPE — WHAT THIS LEMMA DOES *NOT* CLAIM

1. **It does not by itself prove the upper bound of the ceiling.** It supplies the *input* to the
   pinching of the annihilator; the pinching argument is a separate statement and is not
   re-derived here.
2. **It says nothing about `A_k(q) = P_k(q)`,** nor about any module (`C`, `Γ`, `Q`, `W`).
3. **It is not characteristic-free:** `char K ≠ 2` is used, and used essentially, in the count.
4. It describes the singular locus **along a single sheet**. The global singular locus of
   `⋃_J L_J` is the union over `J` of these `D_{k+1}` arrangements; no claim is made here about
   the combinatorics of that union, nor about its intersection lattice.
5. The identification of the swap hyperplanes with the `D_{k+1}` reflection arrangement is stated
   for the *set* of hyperplanes; no claim is made that the `D_{k+1}` Weyl group acts on the
   arrangement `⋃_J L_J` compatibly.

---

## 5. PROVENANCE

- The statement, the `k ≤ 3` proof (twelve hyperplanes by hand) and the lower-side exhibition are
  from the campaign corpus; the scope correction that isolated this lemma as the sole obstruction
  to the uniform finite window is `v8` of the assembly draft, §`GAP 3`.
- The proof for all `k`, the identification with the `D_{k+1}` reflection arrangement, the
  characteristic-`2` caveat, and the machine verification `k ≤ 5`: Lacassagne, this deposit.
- Route: the lemma was reached by parametrising the sheet by one coordinate per matching edge,
  which turns every competing sheet's equation into a two-term relation via `(∗)`. The whole
  content is the two-case split "common edge / not common edge"; nothing deeper is used.

---

**Every statement in this document carries its grade inline.**
**The magic word is not spoken: this lemma closes an input of `GAP 3`, not `GAP 3`.**
