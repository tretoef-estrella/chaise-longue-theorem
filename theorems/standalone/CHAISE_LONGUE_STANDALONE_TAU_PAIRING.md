> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-09-02
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE τ-PAIRING AND THE THREE-PAIR CERTIFICATE* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_STANDALONE_TAU_PAIRING.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# **THE `τ`-PAIRING AND THE THREE-PAIR CERTIFICATE**
### Standalone · `TAU PAIRING v1` · Chaise Longue Campaign · 2026-09-02
### ### 🟢 **Self-contained. Three statements with proofs. What is measured and what is proved are separated line by line.**

---

# 1 · SETUP

`K = F_3`, `q = 3^v`, `k ≥ 2`, `U` an alphabet of `2k` letters, `c_R := (q−2k−1)/2`, and `R := (c_R^k)` the `k × c_R` rectangle. Write `Δ(U)` for the Vandermonde, `s_R(U^2)` for the Schur function of `R` in the squares, and
> ### `g_0 := Δ(U)·s_R(U^2)`,  `Φ_u := u^{q−1}`,  `Θ := ∏_{u∈U}u^{q−1}`.

For a pair `a ≠ b` write `C' := U∖\{a,b\}` and `s_{ab}` for the campaign's generator, with `s_{ba} = −s_{ab}`. The "box" is `K[U]/(u^q)`.

**Banked input.** `SXP-1`: `Δ·s_R(U^2) = Σ_α ± a_{E_α}` over partitions `α ⊆ R`, with `E_α = \{2(α_r+k−r)\}_{r=1}^k ∪ \{2c_R+2s−1−2α_s\}_{s=1}^k`, and `a_E := \det(x_i^{E_j})`.

---

# 2 · `THEOREM E` — THE EXPONENT STRUCTURE OF `g_0` *(`PROVED`, all `k`, all odd `q`)*

> ### `\operatorname{supp}(g_0) = \big\{x^π : π \text{ a permutation of } E ∪ (q−2−E),\ E ⊂ \{0,2,…,q−3\},\ |E| = k\big\}`, **all coefficients `±1`.**
> ### Equivalently: `x^π ∈ \operatorname{supp}(g_0)` **iff its exponent set has `k` even and `k` odd entries, all distinct, all `≤ q−2`, and is closed under `e ↦ q−2−e`.**

**Proof.** Put `e_r := 2(α_r+k−r)`. Then `α_r = e_r/2 − (k−r)`, and the odd part of `E_α` is `2c_R+2s−1−2α_s = 2c_R+2k−1−e_s = q−2−e_s`. Conversely, given `k` distinct evens `e_1 > ⋯ > e_k` in `[0,q−3]`, setting `α_r := e_r/2 − (k−r)` gives a partition (`e_r ≥ e_{r+1}+2`) with `α_k ≥ 0` and `α_1 = e_1/2 − k + 1 ≤ c_R` iff `e_1 ≤ q−3`. So every such `E` occurs, exactly once. Distinct `α` give distinct exponent SETS, hence disjoint monomial supports; and `a_E = \det(x_i^{E_j})` has as monomials exactly the permutations of `E`, with coefficient `±1`. ∎

> ### **COROLLARY E′ — THE COLLAPSE.** For any `π`, exactly one `α` contributes, so
> # `\operatorname{coef}_{x^π}(g_0) = ε_E · \operatorname{sgn}(σ_π)`,
> ### where `E` is the exponent set of `π`, `ε_E` its `SXP` sign, and `σ_π` the permutation sorting `π` into `E`. **No sum over permutations, no Kostka numbers.**
✅ *Verified at `(k,q) = (2,9)`: the `144` monomials of `g_0` fall into `6` classes by exponent set, and within each class `\operatorname{coef}(m)·\operatorname{sgn}(σ_m)` is constant — `6/6`.*

---

# 3 · `THEOREM τ` — UNIQUE FACTORIZATION IS IMPOSSIBLE *(`PROVED`, all `k`)*

Let `f := z^3 s_{ab}` and let `μ = Φ_aΦ_b·ν` be **doubly saturated** (`a`- and `b`-exponents both `q−1`), with `ν` supported on `C'`. Let `τ := (a\,b)`.

> ### **(i)** No factorization `μ = μ_f·μ_g` has `μ_f` with `a`-exponent `q−1` and `b`-exponent `0` (or vice versa): that forces `μ_g` to have `b`-exponent `q−1 > q−2`, impossible by `THEOREM E`.
> ### **(ii)** `τ` maps factorizations of `μ` to factorizations of `τμ = μ`, **preserves the product of coefficients**, and **has no fixed points**.
> # **⟹ The factorizations come in `τ`-pairs of equal sign. Their number is EVEN, and UNIQUE FACTORIZATION IS IMPOSSIBLE on a doubly saturated monomial.**

**Proof of (ii).** `f` is `τ`-antisymmetric, since `s_{ba} = −s_{ab}` and `z^3` is symmetric; `g_0` is `τ`-antisymmetric, since `Δ` is antisymmetric and `s_R(U^2)` symmetric. Hence `\operatorname{coef}_f(τμ_f) = −\operatorname{coef}_f(μ_f)` and `\operatorname{coef}_{g_0}(τμ_g) = −\operatorname{coef}_{g_0}(μ_g)`, so the product is `τ`-invariant. No fixed points: for the surviving types the `a`- and `b`-exponents of `μ_f` differ, because `q−2` is odd. ∎

> ### **COROLLARY.** `\operatorname{coef}_μ(f·g_0) ≡ 2·(\text{signed number of } τ\text{-pairs}) ≡ −(\text{that number}) \pmod 3`.
📊 **MEASURED, and consistent:** at `(2,9)` the minimum number of factorizations of a box monomial is `2` and **all such monomials have coefficient `0`**; the nonzero ones have `6`. At `(3,9)`: minimum `2` (`168` monomials, all `0`); the `48` nonzero ones have **exactly `6`**.

---

# 4 · `THEOREM 3P` — THE THREE-PAIR MONOMIAL *(`PROVED` for `q ≥ 8k−9`, all `k ≥ 2`)*

With `C' = \{c_1,…,c_{2k−2}\}` and `e_j := 4j` for `j = 1..k−2`, set
> ### `μ^* := Φ_a·Φ_b·c_1^2·c_2^{\,q−1}·∏_{j=1}^{k−2}c_{2j+1}^{\,e_j+1}c_{2j+2}^{\,q−1−e_j}`.
> ### Then `μ^*` is a box monomial and its factorizations are **EXACTLY six, forming three `τ`-pairs** `A`, `B`, `C`, with `\operatorname{coef}_f` equal to `−1`, `−1`, `+1` respectively.
> # **⟹ `\operatorname{coef}_{μ^*}(f·g_0) = 2(σ_A+σ_B+σ_C) ≡ −(σ_A+σ_B+σ_C) \pmod 3`, with `σ_X = ±1`.**
> ### **This is nonzero iff `σ_A, σ_B, σ_C` are NOT all equal.** *(Exhaustively: `(+,+,+)` and `(−,−,−)` give `0`; the other six give `±1`.)*

**Proof.** By `THEOREM E`, a candidate `μ_g` is valid iff its exponent set is closed under `e ↦ q−2−e`. Running through the types of `μ_f` (the `D` types are excluded by `THEOREM τ`(i)):
> **`A`** — `μ_g` set `= \{0,q−3,1,q−2\} ∪ \{e_j,q−2−e_j\}`: closed, and distinct because `e_j ∈ [4,q−7]` and `e_j + e_{j'} ≤ 8(k−2) < q−3`. **Valid, one pair.**
> **`B`** — the removed letter must be `c_1`: the partner of `q−4` is `2`, which lies in the set only if `ν_c = 2`. Set `= \{0,q−4,2,q−2\} ∪ \{e_j,q−2−e_j\}`: closed. **Valid, one pair.**
> **`C`** — the cubed letter must be `c_2`: for `c_1` the exponent `ν_c−4 < 0`; for `c_{2j+1}` or `c_{2j+2}` the partner condition forces some `e_{j'} = q−5`, excluded. Set `= \{q−1−i,i+1,q−5,1\} ∪ \text{rest}`; the partner of `q−5` is `3`, forcing `i ∈ \{2,q−4\}` (a `τ`-pair). **Valid, one pair.** ∎

📊 **MEASURED:** `(2,9)` with `μ^* = (8,8,2,8)` and `(2,27)` with `μ^* = (26,26,2,26)` both give exactly `6` factorizations and coefficient `1`, with pair-signs `(+1,−1,−1)`. At `(3,9)` — below the range `q ≥ 8k−9 = 15` — the analogous `μ` with boundary `e`'s has the same six factorizations, and **all `48` nonzero monomials of that cell are of this form.**

---

# 5 · GRADES, AND WHAT IS **NOT** CLAIMED

| statement | grade |
|---|---|
| `THEOREM E` and `COROLLARY E′` | **PROVED**, all `k`, all odd `q` — *the collapse verified `6/6` at `(2,9)`* |
| `THEOREM τ` | **PROVED**, all `k` |
| `THEOREM 3P` | **PROVED** for `q ≥ 8k−9`, all `k ≥ 2` |
| the pair-signs `(σ_A,σ_B,σ_C)` | ### **MEASURED** at `(2,9)`, `(2,27)`, `(3,9)`: `(+1,−1,−1)`. **NOT PROVED for general `k`.** |

⚠️ **What is NOT claimed.**
> ### **(a)** The three signs `∀k`. By `COROLLARY E′` each is `ε_E·\operatorname{sgn}(σ_π)` — an `SXP` sign times an inversion count — so it is a **finite explicit computation, not a new idea**; but it is **not done here.**
> ### **(b)** The range `2k+1 ≤ q < 8k−9`, where the interior `e_j = 4j` do not fit. `(3,9)` shows the same pattern with boundary values, but the general small-`q` case analysis is **not written.**
> ### **(c)** Nothing here addresses the case `3 \mid k`, nor the families of generators indexed by more than two letters.

---
*Standalone `TAU PAIRING v1` · Chaise Longue Campaign. Companion to `SXP-BOUND v1` and `STAR IDENTITY v1`.*
