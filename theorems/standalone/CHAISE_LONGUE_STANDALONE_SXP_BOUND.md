> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-09-02
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *A SHARP FIRST-ROW BOUND FOR s_R[p_2]·s_τ IN FINITELY MANY VARIABLES* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_STANDALONE_SXP_BOUND.md
>
> **Status, as written in the document:** 🟢 Self-contained. `PROVED over `Z`, for every `k ≥ 1`, every ODD `q ≥ 2k+1`, and every `j ∈ {1,…,k}`. Every `PROVED` carries its proof; the boundary of the hypotheses is stated with counterexamples.
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (2 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# **A SHARP FIRST-ROW BOUND FOR `s_R[p_2]·s_τ` IN FINITELY MANY VARIABLES**
### Standalone · `SXP-BOUND v1` · Chaise Longue Campaign · 2026-09-02
### ### 🟢 **Self-contained. `PROVED over `Z`, for every `k ≥ 1`, every ODD `q ≥ 2k+1`, and every `j ∈ {1,…,k}`. Every `PROVED` carries its proof; the boundary of the hypotheses is stated with counterexamples.**

---

# 1 · STATEMENT

Let `k ≥ 1`, let `q` be **odd** with `q ≥ 2k+1`, and set
> ### `c := \dfrac{q-2k-1}{2} \in Z_{≥0}`,  `R := (c^k)` (the `k × c` rectangle),  `τ := (2, 1^{2j-1})` for `1 ≤ j ≤ k`.

Let `Λ` be the ring of symmetric functions over `Z`, `p_2` the second power sum, `s_λ` the Schur function of `λ`, and `f[p_2]` the plethysm (substitution `x_i ↦ x_i^2`).

> # **THEOREM `SXP-1`.** *Every partition `ν` with `ℓ(ν) ≤ 2k+1` and `⟨s_R[p_2]·s_τ,\; s_ν⟩ ≠ 0` satisfies*
> # `ν_1 = 2c+2 = q-2k+1` **exactly**,  and  `ν_2 ≤ q-2k`.
> ### *Moreover `⟨s_R[p_2]·s_τ, s_ν⟩ ∈ \{0, ±1\}` for every such `ν`.*

**The support is explicit:** `ν ↔ (ν^{(0)}, ν^{(1)})` via the `2`-quotient, with `ν^{(0)} ⊆ (c^k)`, `ν^{(0)}_1 = c`, and `ν^{(1)}/μ` a vertical strip of size `j-1`, where `μ` is the `180°`-complement of `ν^{(0)}` in `(c^k)`.

---

# 2 · THE TOOL

**(Littlewood; Wildon, «A generalized SXP rule proved by bijections and involutions», arXiv:1508.07030, *Annals of Combinatorics* (2018), Thm 1.1, with `r = 2`.)** For partitions `ν, τ` and any `f ∈ Λ`:
> ### `⟨s_τ · f[p_2],\; s_ν⟩ = ⟨f,\; φ_2(s_{ν/τ})⟩`,  and  `φ_2(s_{ν/τ}) = ± s_{ν^{(0)}/τ^{(0)}}·s_{ν^{(1)}/τ^{(1)}}`
if `ν` and `τ` have the same `2`-core (computed with the same number of beads), and `0` otherwise. Here `φ_2` is the adjoint of `f ↦ f[p_2]` and `(ν^{(0)},ν^{(1)})` is the `2`-quotient.

**Only the support and the absolute value of the coefficient are used below; the sign convention is Wildon's and plays no role.**

---

# 3 · PROOF

## Step 1 — Abacus set-up with `N = 2k+1` beads

`2k+1` beads represent exactly the partitions with `ℓ(ν) ≤ 2k+1`. *(The `2k`-variable ring kills `ℓ(ν) > 2k`, so this suffices; see §5(a) for why the restriction is essential.)*

The `β`-set of `ν` is `\{ν_i + 2k+1-i\}_{i=1}^{2k+1}`. Runner `0` carries the even positions, runner `1` the odd ones. If runner `0` carries `b_0` beads and runner `1` carries `b_1`, then the runner-`0` positions are `2(ν^{(0)}_r + b_0 - r)` for `r = 1,…,b_0`, and the runner-`1` positions are `2(ν^{(1)}_r + b_1 - r)+1`.

For `τ = (2,1^{2j-1})` with `2k+1` beads:
> ### `β(τ) = \{0,…,2k+2\} ∖ \{2k-2j+1,\; 2k+1\}`, hence `b_0 = k+2`, `b_1 = k-1`, and
> ### `τ^{(0)} = ∅`,  `τ^{(1)} = (1^{j-1})`,  `2\text{-core}(τ) = (2,1)`.

**This requires `j ≤ k`**, so that `(1^{j-1})` fits on a runner with `k-1` beads — exactly the range of the generators involved.

## Step 2 — Which `ν` can appear, and why every coefficient is `±1`

By the tool, `⟨s_R[p_2]·s_τ, s_ν⟩ = ± ⟨s_{(c^k)},\; s_{ν^{(0)}}·s_{ν^{(1)}/(1^{j-1})}⟩` for `ν` with core `(2,1)` and the same bead counts. Expanding `s_{ν^{(1)}/(1^{j-1})} = Σ_μ c^{ν^{(1)}}_{(1^{j-1}),μ}\,s_μ`:
> ### coefficient `= ± Σ_μ c^{ν^{(1)}}_{(1^{j-1}),μ}\;c^{(c^k)}_{ν^{(0)},μ}`.

**Rectangle Littlewood–Richardson rule:** `c^{(c^k)}_{ν^{(0)},μ} ≠ 0` iff `ν^{(0)} ⊆ (c^k)` and `μ` is the `180°`-rotated complement of `ν^{(0)}` in `(c^k)`, i.e. `μ_r = c - ν^{(0)}_{k+1-r}`; and in that case it equals `1`.
> ### **⟹ AT MOST ONE `μ` CONTRIBUTES**, and the coefficient is `± c^{ν^{(1)}}_{(1^{j-1}),μ} ∈ \{0,±1\}` — by Pieri it is `1` exactly when `ν^{(1)}/μ` is a vertical strip of size `j-1`. ∎ *(This is the coefficient statement.)*

## Step 3 — The bead count, which is the whole point

`ν^{(1)}` lives on runner `1`, which carries only `b_1 = k-1` beads, so `ℓ(ν^{(1)}) ≤ k-1`. Since `μ ⊆ ν^{(1)}` (vertical strip), also `ℓ(μ) ≤ k-1`, i.e. `μ_k = 0`. But `μ_k = c - ν^{(0)}_1`. Therefore
> # `ν^{(0)}_1 = c` — **the first row of `ν^{(0)}` is FULL, and it is forced.**

Hence the top bead of runner `0` sits at `2(ν^{(0)}_1 + b_0 - 1) = 2(c+k+1) = q+1`, using `2c = q-2k-1`. And every runner-`1` bead is at most `2(ν^{(1)}_1 + k-2)+1 ≤ 2(c+1+k-2)+1 = q-2`, using `ν^{(1)}_1 ≤ μ_1 + 1 ≤ c+1`. So `\max β = q+1` exactly, and with `2k+1` beads
> ### `ν_1 = (q+1) - 2k = q-2k+1 = 2c+2`. ∎

For the second row: the second-largest bead is at most `\max\{2(c+k),\; q-2\} = q-1`, so `ν_2 ≤ q-1-(2k-1) = q-2k`. ∎

> ### ⭐ **The mechanism in one sentence: runner `1` is too short, which forces the first row of the rectangle to be full, which pins the top bead at `q+1` — and hence `ν_1` exactly.**

---

# 4 · COROLLARIES

## `SXP-2` — membership in a monomial ideal *(`PROVED`, same scope)*

In `2k` variables `U`, with `Δ(U)` the Vandermonde and `δ = (2k-1,…,0)`:
> ### `Δ(U)·s_R(U^2)·s_τ(U) = Σ_ν c_ν\,a_{ν+δ}(U)`, and `a_{ν+δ} ∈ (u^q)` iff `ν_1 + 2k-1 ≥ q` iff `ν_1 ≥ q-2k+1`.
Every `c_ν ≠ 0` has `ν_1 = q-2k+1` by `SXP-1`, hence
> # `Δ(U)·s_R(U^2)·s_τ(U) \;∈\; (u^q : u ∈ U)` **over `Z`.**
Since the ideal is **monomial**, the same holds after reduction modulo any prime. Moreover `ν_1 > ν_2`, so the exponent `q` occurs **exactly once** in each monomial of `a_{ν+δ}`; expanding each alternant along that unique top exponent gives
> ### `= ± Σ_i (-1)^{i-1} x_i^{\,q}·Δ(U∖x_i)·G_j(U∖x_i)`, with `G_j` symmetric in the remaining `2k-1` letters and independent of `x_i`. ∎

## `SXP-3` — nothing is lost modulo `p` *(`PROVED`)*

Steps 1–3 are statements about **bead positions** (integers) and **Littlewood–Richardson / Pieri multiplicities**, all `0` or `1`. Step 4 is a monomial-ideal statement. There is no division, no cancellation between distinct `ν`, and no coefficient that can become `0` modulo a prime. **The only cancellations occur inside `Λ` over `Z`, in the LR expansion, and they are already accounted for by the `±1` output.** ∎

---

# 5 · THE BOUNDARY OF THE HYPOTHESES *(with counterexamples)*

**(a) The length restriction `ℓ(ν) ≤ 2k+1` is essential.** In infinitely many variables, constituents with small first row do appear: for `k=1`, `c=1`,
> ### `p_2·s_{(2,1)} = s_{(4,1)} - s_{(2,1,1,1)}`,
and the second has first row `2 < 4` — but **four parts**. The `2k`-variable ring kills it, and the abacus with `2k+1` beads encodes exactly that.

**(b) The multiplication by `s_τ` is essential.** `s_R[p_2]` alone violates the bound badly: for `k=1`, `q=9`, `h_3[p_2]` contains `s_{(3,3)}`, first row `3 < 8`. **The bound holds by massive cancellation in the product, not by any margin.** *(A "multiply at the end and keep the margin" argument is therefore refuted.)*

**(c) `j ≤ k` is essential.** For `j > k`, `τ^{(1)}` would need `j-1` beads on a runner carrying `k-1`: no such `ν` exists — consistent with the corresponding generator vanishing in `2k` letters.

**(d) `q` odd is needed** for `c` to be an integer; **`q ≥ 2k+1`** for `R` to exist. **Nothing else about `q` is used** — in particular, **no assumption that `q` is a prime power.**

---

# 6 · GRADES

| statement | grade |
|---|---|
| **`SXP-1`** (first row exactly `q-2k+1`; `ν_2 ≤ q-2k`; coefficients `±1`) | **PROVED over `Z`**, all `k ≥ 1`, all odd `q ≥ 2k+1`, all `j ≤ k` |
| **`SXP-2`** (membership in `(u^q)`, and the Laplace form) | **PROVED**, same scope, any characteristic |
| **`SXP-3`** (nothing is lost mod `p`) | **PROVED** |
| The boundary statements of §5 | **PROVED** (explicit counterexamples) |
| Gates | **MEASURED**, 19 cells, all TRUE, by direct expansion in `2k` variables |

⚠️ **Scope note.** The theorem is a statement about symmetric functions; it makes no reference to the campaign's geometry. Its use there requires the separately established equivalence between membership in `(u^q)` and the Schur bound, which is **not** re-derived here.

---
*Standalone `SXP-BOUND v1` · Chaise Longue Campaign. Companion to `LDL-SHARP v1`, `CONJECTURE R v1`, `THEOREM OMEGA v1`, `JORDAN REDUCTION v2` and `SNAP THEOREMS v2`.*
