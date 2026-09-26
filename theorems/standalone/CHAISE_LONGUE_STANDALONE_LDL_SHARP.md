> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-09-01
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE LOW DEGREE LAW, SHARP — LDL-SHARP* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_STANDALONE_LDL_SHARP.md
>
> **Status, as written in the document:** 🟢 Self-contained. Every object defined here. `PROVED for all k ≥ 1 and all odd q`.
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (2 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# **THE LOW DEGREE LAW, SHARP** — `LDL-SHARP`
### Standalone · Chaise Longue Campaign · 2026-09-01 · Don Mister Grep, auditor
### ### 🟢 **Self-contained. Every object defined here. `PROVED for all k ≥ 1 and all odd q`.**

---

# 1 · SETUP

Let `K = F_3`, `n = 2k+2`, `q = 3^v`, and `S = K[x_0, …, x_{n−1}]` with the standard grading. Write `e_d` for the elementary symmetric polynomial of degree `d` and
> ### `E := (e_1, e_3, e_5, …, e_{2k+1})` — **the ODD elementary symmetric polynomials only** — an ideal with `k+1` generators.

`E` is **radical** in characteristic `≠ 2`, and `E = ⋂_J I_J` over the `(2k+1)!!` perfect matchings `J` of `{0,…,n−1}`, with `I_J = (x_a + x_b : {a,b} ∈ J)` a linear prime; each **leaf** `V_J` is a linear subspace of dimension `k+1`. For odd `q` one has `#V(E)(F_q) = P_k(q)`, a polynomial of degree `k+1` with leading coefficient `(2k+1)!!`.

**The slice.** Put `S' := K[x_0, …, x_{2k}]`, `E'_k := (e_1, e_3, …, e_{2k+1})` in `S'`, and
> ### `V_1 := V(E)(F_q) ∩ {x_n = 1}`, a finite set of `N_k(q)` points in `A^{2k+1}`.

Let `I(V_1) ⊆ S'` be its vanishing ideal and `gr I(V_1)` the ideal of top forms. In the vocabulary of **orbit harmonics** (Li–Liu–Rhoades, arXiv:2607.28157, Def. 1.2), `R(V_1) := S'/gr I(V_1)` is the **orbit harmonics ring** of the locus `V_1`, and we write
> ### `h_{V_1}(d) := dim_K R(V_1)_d`.

Since `V_1` is a reduced finite point set, `Σ_d h_{V_1}(d) = N_k(q)`.

---

# 2 · THE THEOREM

> # **THEOREM (`LDL-SHARP`).** *For every `k ≥ 1` and every odd `q`:*
> ### **(i)** `h_{V_1}(d) = HF(S'/E'_k)_d` **for all `0 ≤ d ≤ q−1`**, where
> ### `HF(S'/E'_k)_d = [t^d] ∏_{i=2}^{k+1} (1 − t^{2i−1}) / (1 − t)^{2k}`;
> ### **(ii)** `HF(S'/E'_k)_q − h_{V_1}(q) ≥ 2k`.

**In words: the orbit harmonics ring of the slice agrees with the complete-intersection quotient in every degree below `q`, and it drops by at least `2k` at degree `q` exactly. The boundary is `q`, and it is sharp.**

---

# 3 · PROOF

## 3.1 · Part (i): agreement below `q`

Each leaf `V_J` meets `{x_n = 1}` in an affine `k`-plane `Λ_J`, and `Λ_J(F_q) ≅ F_q^k` is a full grid: on `V_J` the coordinate `x_n` is free, so `x_n = 1` freezes the pair containing `n` to `(1, −1)` and leaves `k` free coordinates. Hence `V_1 = ⋃_J Λ_J(F_q)`.

**Cap Lemma (Chevalley/Combinatorial Nullstellensatz).** *A polynomial of total degree `< q` vanishing on all `F_q`-points of an affine `k`-plane vanishes on the plane.*
Indeed, in affine coordinates `y_1,…,y_k` on the plane the polynomial has degree `< q` in total, hence degree `≤ q−1` in each variable, and a polynomial of degree `≤ q−1` in each variable vanishing on `F_q^k` is zero.

Therefore, in degrees `< q`, a polynomial vanishing on `V_1` vanishes on `⋃_J Λ_J` as a variety, i.e. `I(V_1)` and `I(⋃_J Λ_J) = G_k` agree below degree `q`. Since `gr G_k = E'_k` (the leaf arrangement of the slice has the odd elementary symmetric functions as its top-form ideal), part (i) follows. ∎

## 3.2 · Part (ii): the drop at `q`, and its size

For each `i`, the polynomial `x_i^q − x_i` vanishes on every `F_q`-point, hence lies in `I(V_1)`; its top form is `x_i^q`, so
> ### `x_i^q ∈ gr I(V_1)` for every `i = 0, …, 2k`.

There are `2k+1` such pure powers in `S'`. They satisfy **exactly one linear relation modulo `E'_k`**: in characteristic 3 with `q = 3^v`, Frobenius gives
> ### `Σ_{i=0}^{2k} x_i^q = (Σ_{i=0}^{2k} x_i)^q = e_1^q`,
and `e_1 ∈ E'_k`, so `e_1^q ∈ E'_k`.

Conversely, suppose `Σ_i c_i x_i^q ∈ E'_k`. Let `W_J` denote the direction space of the affine leaf `Λ_J`. If `g ∈ G_k` then for `p ∈ Λ_J` and `w ∈ W_J` the polynomial `t ↦ g(p + tw)` vanishes identically, so its leading coefficient `g_top(w)` vanishes; hence every top form of `G_k` — that is, every element of `E'_k` — vanishes on `⋃_J W_J`. Now take `i ≠ j` in `{0,…,2k}`; since `n = 2k+2 ≥ 4` there is a matching `J` pairing `i` with `j`, and `W_J` contains the vector `w` with `w_i = 1`, `w_j = −1` and all other coordinates `0`. Evaluating `Σ_i c_i x_i^q` at `w` gives `c_i − c_j = 0` (using `q` odd). Hence all `c_i` are equal, and the relation is the Frobenius one.

Therefore the pure powers span a space of dimension exactly `(2k+1) − 1 = 2k` modulo `(E'_k)_q`, and all of it lies in `(gr I(V_1))_q`. Consequently
> ### `dim (gr I(V_1))_q − dim (E'_k)_q ≥ 2k`, i.e. `HF(S'/E'_k)_q − h_{V_1}(q) ≥ 2k`. ∎

---

# 4 · SCOPE, SHARPNESS AND CHARACTERISTIC

- **Scope:** all `k ≥ 1`, all odd `q`; part (ii) as stated uses `q = p^v` with `p = char K` (Frobenius additivity) and `q` odd.
- **Sharpness:** the boundary cannot be moved past `q`. The obstruction is named and explicit — the pure powers `x_i^q` — and the drop is bounded below by `2k`.
- **Characteristic 0:** the statement has no characteristic-0 analogue: there is no `q` and no box, and step 3.2 uses `x^q − x` and Frobenius additivity.
- **`q` even:** excluded throughout. The identification `#V(E)(F_q) = P_k(q)` already requires `−1 ∈ μ_{q−1}`, i.e. `q` odd.

---

# 5 · MEASURED CONSEQUENCES *(gates, not part of the proof)*

| cell | first divergence degree | drop at `q` |
|---|---|---|
| `(1,3)`, `(1,9)` | `q` | `3 = 2k+1` |
| `(2,3)`, `(2,9)` | `q` | `4 = 2k` |
| `(3,3)` | `q` | `6 = 2k` |
| `(4,3)` *(new terrain)* | `q` | `8 = 2k` |

**The lower bound `≥ 2k` is an equality in all measured cells with `k ≥ 2` (4/4); at `k = 1` the drop is `2k+1 = 3` because `h_{V_1}(q) = 0` there.**

Slice `h`-vectors, `q = 3`: `k=1`: `(1,2,3)`; `k=2`: `(1,4,10,15,15)`; `k=3`: `(1,6,21,49,84,105,91)`; `k=4`: `(1,8,36,111,258,468,672,750,603)`. Sums `6, 45, 357, 2907 = N_k(3)`.

---

# 6 · POSITION IN THE LITERATURE

Two independent literature sweeps found no precedent for a statement of the form *"the Hilbert function of a finite `F_q`-point set agrees with a complete-intersection quotient up to degree `q + c`, with `c` independent of `q`"*. The nearest neighbours are:

- **Wilson (1990)**, diagonal forms of incidence matrices over any field, giving affine Hilbert functions of **symmetric** subsets of the boolean cube;
- **Hegedűs–Rónyai**, reduced Gröbner bases of a single layer, over any field;
- **Venkitesh** (arXiv:2111.06993), affine Hilbert functions of unions of layers in uniform grids — **over `R`**, with layers cut by coordinate sums;
- **Geil–Høholdt**, the *footprint* bound — an inequality on zero counts, not an equality up to a degree.

None gives a `q + constant` boundary. Within orbit harmonics (Rhoades and collaborators), every locus studied to date is **combinatorial** — `0/1` matrices, or integer points of polytopes — and none is the set of `F_q`-points of a variety.

---
*Standalone `LDL-SHARP v1` · Chaise Longue Campaign · all statements graded; §2 is `PROVED`, §5 is `MEASURED`.*
