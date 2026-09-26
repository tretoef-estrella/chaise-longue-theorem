> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-09-01
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *A PRESENTATION OF THE ORBIT HARMONICS RING OF A NEGATION-CLOSED F_q-LOCUS* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_STANDALONE_CONJECTURE_R.md
>
> **Status, as written in the document:** Standalone · `CONJECTURE R` · Chaise Longue Campaign · 2026-09-01
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (1 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# **A PRESENTATION OF THE ORBIT HARMONICS RING OF A NEGATION-CLOSED `F_q`-LOCUS**
### Standalone · `CONJECTURE R` · Chaise Longue Campaign · 2026-09-01
### ### 🟢 **Self-contained. `THEOREM P` and `THEOREM N` are `PROVED for all k, all odd q`. The presentation itself is `MEASURED 5/5` and stated as a conjecture.**

---

# 1 · SETUP AND VOCABULARY

`K = F_3`, `n = 2k+2`, `q = 3^v` odd, `S' = K[x_0,…,x_{2k}]`, `m'^{[q]} = (x_0^q,…,x_{2k}^q)`, and
> ### `E'_k := (e_1, e_3, …, e_{2k+1})` — the **odd** elementary symmetric polynomials.

`V_1 := V(E)(F_q) ∩ {x_n = 1}` is a finite set of `N_k(q)` points; `I(V_1)` its vanishing ideal; `gr I(V_1)` the ideal of top forms; and, in the vocabulary of **orbit harmonics** (Li–Liu–Rhoades, arXiv:2607.28157, Def. 1.2),
> ### `R(V_1) = S'/gr I(V_1)` is the **orbit harmonics ring** of `V_1`.

⚠️ **Distinction from the literature.** Liu–Ma–Rhoades–Zhu (arXiv:2409.06175) study orbit harmonics for **perfect matchings** `PM_n`, but as `0/1` **matrices over `C`**; their Hilbert series relates to Tracy–Widom distributions and refines the plethysm `h_{n/2}[h_2]`. **Our locus is a set of `F_q`-points of a variety, not a matrix locus, and our field is finite. The objects are different; the framework is the same.**

---

# 2 · THE THREE SOURCES

A point lies in `V(E)(F_q)` **iff its coordinate multiset is closed under negation**. On the slice `x_n = 1`, that splits without remainder into three conditions on `(x_0,…,x_{2k})`:

| | condition | name | symmetric under `x ↦ −x`? |
|---|---|---|---|
| **(1)** | `mult(0)` is **EVEN** | **PARITY** | yes |
| **(2)** | `mult(c) = mult(−c)` for `c ≠ 0, ±1` | **BALANCE** | yes |
| **(3)** | `#{x_i = −1} = #{x_i = 1} + 1` | **ANCHOR** | **no** |

**Verified `5/5` by direct count:** `(1,3) → 6`, `(2,3) → 45`, `(3,3) → 357`, `(1,5) → 12`, `(1,7) → 18`, all equal to `N_k(q)`. *(The count is exact precisely because the description is complete: a missing or superfluous condition would not reproduce `N_k`.)*

⚠️ **Degenerate case:** over `F_3 = {0,1,−1}` there is no `c` outside `{0, ±1}`, so **BALANCE is empty at `q = 3`**. From `q = 9` onward there are `(q−3)/2` balance families.

---

# 3 · `THEOREM P` — THE PARITY DETECTORS *(`PROVED`, all `k`, all odd `q`)*

For disjoint subsets `A, B ⊆ {0,…,2k}` with `T = A ∪ B` and `T^c` the complement, define
> # `G_{A,B} := (∏_{l ∈ T^c} x_l) · [ (−1)^{|A|} ∏_{a ∈ A} (1 + x_a^{q−1}) − (−1)^{|B|} ∏_{b ∈ B} (1 + x_b^{q−1}) ]`.

> ### **THEOREM P.** `G_{A,B} ∈ I(V_1)`, its top form is not in `m'^{[q]}`, and its degree is `|T^c| + max(|A|,|B|)·(q−1)`.

**Proof.** Over `F_q`, `1 + x^{q−1}` equals `2 = −1` when `x ≠ 0` and `1` when `x = 0`. Hence `(−1)^{|A|}∏_A(1+x_a^{q−1}) = (−1)^{z_A}`, where `z_A` is the number of zero coordinates in `A`; likewise for `B`. The bracket therefore equals `(−1)^{z_A} − (−1)^{z_B}`, which is nonzero **iff `z_A` and `z_B` have opposite parity, iff `z_T` is odd**. The prefactor `∏_{T^c} x_l` is nonzero iff no zero coordinate lies outside `T`, i.e. iff `z_T` is the total number of zeros. So `G_{A,B}(P) ≠ 0` forces an **odd total number of zero coordinates**, which condition (1) forbids. Degrees and top forms are read off: the larger block dominates; for `|A| = |B|` the two top monomials `x_{T^c}x_A^{q−1}` and `x_{T^c}x_B^{q−1}` are distinct. Every exponent lies in `{0, 1, q−1}`, so no top form is in `m'^{[q]}`. ∎

**Special case:** `G_{\{i\},\{j\}} = (∏_{l ≠ i,j} x_l)(x_j^{q−1} − x_i^{q−1})`, of degree exactly `q + 2k − 2`.
⚠️ At `q = 3` **all** balanced detectors live in the single degree `2k+1 = q+2k−2`; for `q > 3` they spread over `q+2k−2`, `2q+2k−5`, `3q+2k−8`, ….

---

# 4 · `THEOREM N` — THE ANCHOR IS NOT A SOURCE *(`PROVED`, all `k`, all `q`)*

**(i)** With value indicators `a_i = [x_i = 1] = 1 − (x_i−1)^{q−1}` and `b_i = [x_i = −1]`, the anchor relation `Σ_i (b_i − a_i) = 1` reduces over `F_3` with `q = 3^v` to
> ### `−(p'_1 + p'_3 + ⋯ + p'_{q−2}) = 1`, where `p'_m = Σ_{i ≤ 2k} x_i^m`,
using `(1+x)^{q−1} = (1+x^q)/(1+x) = Σ_j (−1)^j x^j` in `F_3[x]`. Every **odd** power sum lies in the ideal generated by `E'_k` (odd power sums vanish on `V(E)`, which is radical). Hence the anchor relation is a consequence of the given generators and its top form contributes nothing new.

**(ii)** Any polynomial vanishing on `V_1` *only* because the anchor count fails has the shape `∏_{i ∈ T}(x_i+1) · ∏_{l ∉ T}(x_l^2 − 1)`, of degree `4k + 2 − |T|`, **independent of `q`**.

> ### **The mechanism, and it is pure degree arithmetic: anchor detectors cost degree `2` or `q−1` per coordinate; parity detectors cost `1`. The cheap ones win.** ∎

**Gate:** adding all anchor detectors changes no Hilbert function in any of the five measured cells.
**What the anchor does do** is fix *which* coordinate equals `−1` — it selects the leaf. That is geometry of `V_1`, and it yields a recursion `k → k−1` (treated elsewhere), not new top forms.

---

# 5 · `CONJECTURE R` — THE PRESENTATION *(`MEASURED 5/5`, `q = 9` included)*

> # `gr I(V_1) = E'_k + m'^{[q]} + (\text{top forms of all } G_{A,B})`
> ### equivalently
> # `R(V_1) = S' / ( e_1, e_3, …, e_{2k+1};\ x_0^q, …, x_{2k}^q;\ \text{PARITY DETECTORS} )`.

**Gate.** `(1,3)`, `(1,9)`, `(2,3)` — the two-index detectors `P_{ij}` alone suffice. `(2,9)` — the two-index detectors reproduce all **19** degrees of the measured `h`-vector exactly. `(3,3)` — the residue in degree `7` goes `36 → 21` with `P_{ij}`, and `→ 0` once detectors with `|T| ≤ 4` are included.

---

# 6 · MODULE STRUCTURE *(`MEASURED`; traces over `F_3`)*

The balanced detectors of support `2t` appear to span the irreducible `S_{2k+1}`-representation
> ### `(2k+1−2t,\; 2t−1,\; 1)`.

| `k` | decomposition of the residue in degree `q+2k−2` | total |
|---|---|---|
| `1` | `(1,1,1) = 1` | `1` |
| `2` | `(3,1,1) = 6` | `6` |
| `3` | `(5,1,1) = 15 + (3,3,1) = 21` | `36` |
| `4` | `(7,1,1) = 28 + (5,3,1) = 162` | **`190`** *(prediction)* |

⚠️ **Three points only; and characters were computed as traces mod 3, which rules candidates in or out but cannot separate characters congruent mod 3. The module need not be semisimple in characteristic 3.**

---

# 7 · WHAT IS PROVED AND WHAT IS NOT

| statement | grade |
|---|---|
| `THEOREM P` (parity detectors lie in `I(V_1)`, with degrees) | **PROVED, all `k`, all odd `q`** |
| `THEOREM N` (the anchor supplies no cheap top forms) | **PROVED, all `k`, all `q`** |
| The three-source description of `V_1` | **PROVED** *(it is the definition)*, verified `5/5` |
| `CONJECTURE R` (the presentation) | **MEASURED 5/5** — an upper bound on `gr I(V_1)` remains to be proved |
| Module structure `(2k+1−2t, 2t−1, 1)` | **MEASURED 3/3** |
| Non-membership of `P_{ij}` in `E'_k + m'^{[q]}` | **PROVED for `k=1`**, gated for `k = 2, 3` |

Nothing is claimed in characteristic 2, nor for even `q`.

---
*Standalone `CONJECTURE R v1` · Chaise Longue Campaign. Follows the template of arXiv:2608.27438: generators of the orbit harmonics ideal ⟹ Hilbert series ⟹ graded Frobenius.*
