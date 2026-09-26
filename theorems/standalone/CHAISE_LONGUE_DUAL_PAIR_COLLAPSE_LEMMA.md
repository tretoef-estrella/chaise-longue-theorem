> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026 (date not stated in the document)
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE_LONGUE_DUAL_PAIR_COLLAPSE_LEMMA_v1* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_DUAL_PAIR_COLLAPSE_LEMMA.md
>
> **Status, as written in the document:** Grade: PROVED ∀k (char ≠ 2; stated over `F_3`). Byte-gated at `(k,q) = (1,3),(1,5),(2,3)`.
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (1 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE_LONGUE_DUAL_PAIR_COLLAPSE_LEMMA_v1
### Standalone theorem · Constructor: Lacassagne · campaign Chaise Longue · GAP 3 (Matlis-dual descent)
### Grade: **PROVED ∀k** (char ≠ 2; stated over `F_3`). Byte-gated at `(k,q) = (1,3),(1,5),(2,3)`.

---

## Statement

Let `S = F_3[x_0,…,x_{n−1}]`, `n = 2k+2`, `B = S/m^{[q]}` with `m^{[q]} = (x_0^q,…,x_{n−1}^q)`
(Gorenstein artinian). Let `E = (e_1,e_3,…,e_{2k+1})` (odd elementary symmetrics) and
`M = ann_B(E·B)`. For distinct `a,b ∈ {0,…,2k}` put the independent linear forms
`ℓ_a = x_a + x_{n−1}`, `ℓ_b = x_b + x_{n−1}`, and

`B'' := B/(ℓ_a,ℓ_b)B ≅ F_3[x_i : i∉{a,b}]/(x_i^q)`  (a box ring in `n−2 = 2(k−1)+2` variables,
via `x_a,x_b ↦ −x_{n−1}`),  and  `Ê_j :=` image of `e_j` in `B''` (i.e. `e_j` with `x_a,x_b ↦ −x_{n−1}`),
`Ê = (Ê_1,Ê_3,…,Ê_{2k+1})`.

> **THEOREM (dual pair-collapse).** Multiplication by `(ℓ_aℓ_b)^{q−1}` induces an `F_3`-linear
> isomorphism
> ### `ann_{B''}(Ê·B'')  ⟶^{∼}  M ∩ ann_M(ℓ_a) ∩ ann_M(ℓ_b)`. ###
> Hence `dim( M ∩ ann_M(ℓ_a) ∩ ann_M(ℓ_b) ) = dim ann_{B''}(Ê·B'') = dim( B''/Ê·B'' )`
> (the last equality by Matlis duality in the Gorenstein ring `B''`).

**Corollary (the twist formula).** Writing `z = x_{n−1}` and `e_m^{(k−1)}` for the elementary
symmetrics of the `2k` variables of `B''`, over `F_3`:
### `Ê_j = e_j^{(k−1)} + z·e_{j−1}^{(k−1)} + z²·e_{j−2}^{(k−1)}` ###
(the generating function acquires the factor `(1−zτ)²`, because two of the `n` slots are set to `−z`
while `z` itself remains a variable of `B''`).

---

## Proof (∀k)

1. **Linear-form annihilators are principal.** `m^{[q]}` is `GL_n`-stable over the perfect field `F_3`
   (`(∑c_ix_i)^q = ∑c_i^q x_i^q ∈ m^{[q]}`), so for any linear form `ℓ`, `ann_B(ℓ) = ℓ^{q−1}B`, and
   for independent `ℓ_a,ℓ_b`, `ann_B(ℓ_a)∩ann_B(ℓ_b) = ann_B((ℓ_a,ℓ_b)) = (ℓ_aℓ_b)^{q−1}B`.
   Multiplication by `(ℓ_aℓ_b)^{q−1}` is an isomorphism `B'' = B/(ℓ_a,ℓ_b)B ⟶^{∼} (ℓ_aℓ_b)^{q−1}B`
   (its kernel is `ann_B((ℓ_aℓ_b)^{q−1}) = (ℓ_a,ℓ_b)B`).

2. **The generators collapse.** For any lift `c` of an element of `B''` and any `j`,
   `e_j·(ℓ_aℓ_b)^{q−1}c = Ê_j·(ℓ_aℓ_b)^{q−1}c` in `B`, because `e_j − Ê_j ∈ (ℓ_a,ℓ_b)B` and
   `(ℓ_aℓ_b)^{q−1}·(ℓ_a,ℓ_b)B = 0` (as `ℓ_a^q = ℓ_b^q = 0` in `B`).

3. **Membership transfers.** Therefore `(ℓ_aℓ_b)^{q−1}c ∈ M` `⟺` `Ê_j·(ℓ_aℓ_b)^{q−1}c = 0 ∀j`
   `⟺` `(ℓ_aℓ_b)^{q−1}(Ê_j c) = 0 ∀j` `⟺` `Ê_j c = 0` in `B''` `∀j` (mult by `(ℓ_aℓ_b)^{q−1}`
   injective on `B''`) `⟺` `c ∈ ann_{B''}(Ê·B'')`.

4. **Target identification.** Every element of the image is annihilated by `ℓ_a` and `ℓ_b`
   (`ℓ_a(ℓ_aℓ_b)^{q−1} = ℓ_a^qℓ_b^{q−1} = 0`); and `M ∩ ann_M(ℓ_a) ∩ ann_M(ℓ_b)
   = M ∩ (ℓ_aℓ_b)^{q−1}B` (Matlis `6.5'`) is exactly that image. ∎

**Why this is the DUAL, not the restriction grave.** The map goes `B''`-side `→` `M`-side by
*multiplication* by `(ℓ_aℓ_b)^{q−1}` (the socle/annihilator direction). It never restricts `M` to a
hyperplane. The dead route `ρ(M)` (`FROBENIUS_CONFINEMENT_v3 §5.5–5.6`) restricts `M` and lands
**properly** (`42` of `57` at `k=2→1`); this lemma lands **cleanly** — see the gate.

---

## Gate (`F_3`, control cells; independent, byte-exact)

Engine `step1_dual_descent_lacassagne.py`. For each cell it computes the full-`B` triple
`r_2 = dim(M ∩ ann_M(ℓ_0) ∩ ann_M(ℓ_1))` and the dual side `dim ann_{B''}(Ê·B'')`:

| `k→k−1`, `q` | `r_2` (full `B`) | `dim ann_{B''}(Ê·B'')` | match |
|---|---:|---:|:--:|
| 1→0, q=3 | 3 | 3 | ✓ |
| 1→0, q=5 | 5 | 5 | ✓ |
| 2→1, q=3 | 19 | 19 | ✓ |

Twist formula `Ê_j = e_j + z e_{j−1} + z² e_{j−2}` verified against the substituted generators at all
cells (e.g. `k=1→0,q=3`: `Ê_1 = x_2 − x_3`, `Ê_3 = −x_2 x_3²`).

---

## Scope — what it does and does NOT do

- **Does (PROVED ∀k):** reduces the Matlis pair-annihilator `M ∩ ann_M(ℓ_a) ∩ ann_M(ℓ_b)` to a single
  box-ring quotient `B''/Ê·B''` in `2(k−1)+2` variables — dually, avoiding the restriction grave.
- **Does NOT:** it does **not** identify `B''/Ê·B''` with `M_{k−1}`. Measured (`step1`): the two are
  **equidimensional but distinct** as modules (`ann_{B''}(Ê) ≠ M_{k−1}`; union-rank `5,9,31` vs
  `3,5,19`). The naive "`≅ M_{k−1}`" is **false**; the true residual is the value identity
  `dim(B''/Ê·B'') = A_{k−1}(q)` `∀k`, i.e. that the `(1−zτ)²`-twist preserves the odd-symmetric-plus-box
  Hilbert function (graded-equal `[1,3,6,6,3]` measured at `k=2→1,q=3`; **CANDIDATE ∀k**, open).
- Does not close `(I')`, the increment, or GAP 3; `G` stays 3.

**Engines:** `step1_dual_descent_lacassagne.py`, `matlis_gate_lacassagne.py`.
**Depends on:** `MATLIS_IDENTIFICATION_v1` (`6.5'`), `m^{[q]}` `GL_n`-stability (Matlis Lemma 1.2).
**Avoids:** `FROBENIUS_CONFINEMENT_v3 §5.5` (the restriction grave).

— Lacassagne
