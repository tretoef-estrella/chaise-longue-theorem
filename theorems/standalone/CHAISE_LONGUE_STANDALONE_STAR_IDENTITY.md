> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-09-02
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE STAR IDENTITY* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_STANDALONE_STAR_IDENTITY.md
>
> **Status, as written in the document:** 🟢 Self-contained. Five statements, each with its proof written out. The three places where characteristic 3 is consumed are marked individually. Nothing is graded `PROVED` without a proof here.
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (1 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# **THE STAR IDENTITY**
### Standalone · `STAR IDENTITY v1` · Chaise Longue Campaign · 2026-09-02
### ### 🟢 **Self-contained. Five statements, each with its proof written out. The three places where characteristic 3 is consumed are marked individually. Nothing is graded `PROVED` without a proof here.**

---

# 1 · SETUP

Let `K = F_3`, `q = 3^v`, `k ≥ 1`. Let `U` be an alphabet of `2k` letters, `S' = K[U]`, and
> ### `B := S'\big/\big(e_1(U)\text{-eliminated relations},\ u^q : u ∈ U\big)`, with `z := −e_1(U)` acting nilpotently, `z^q = 0`.

**The relations of `B`, in the form used throughout:** `\;e_{2j+1}(U) + z\,e_{2j}(U) = 0` for `j = 0,…,k`. Write `W := U ∪ \{z\}`, an alphabet of `2k+1` letters on which `B` is `S_{2k+1}`-symmetric, with `e_1(W) = 0`.

**Local notation for a pair.** Fix `a ≠ b` in `U` and put
> ### `C' := U∖\{a,b\}`,  `ê_m := e_m(C')`,  `s := a+b`,  `p := ab`,  `A_m := ê_m + z·ê_{m−1}`  (`A_0 = 1`, `A_{−1} = 0`).

Since `|C'| = 2k−2`, we have `ê_{2k−1} = ê_{2k} = 0`.

**The generators.** `Φ_u := u^{q−1}`; `h_{ab} := Σ_{i=0}^{q−2}a^i(−b)^{q−2−i}`, so `(a+b)h_{ab} = Φ_a − Φ_b`; `ε_{ab} := ê_{2k−2} + s·ê_{2k−3}`; and
> ### `s_{ab} := h_{ab}·ε_{ab}`,  with `s_{ba} = −s_{ab}`,  and the **star sums** `σ_a := Σ_{b≠a} s_{ab}`.

**Banked input.** `LEMMA 0` (`SNAP THEOREMS v2`): `z·e_{2k}(U) = 0`. `LEMMA P`: `p_{2r+1}(U) = −z^{2r+1}` in `B`.

---

# 2 · `LEMMA R` — THE THREE-TERM RECURSION *(`PROVED`, all `k`, all `q`; no box, no characteristic)*

> ### For `j = 0,…,k`: `\;A_{2j+1} + s·A_{2j} + p·A_{2j−1} = 0`.

**Proof.** Splitting the letters `a,b` off `U` gives `e_m(U) = ê_m + s·ê_{m−1} + p·ê_{m−2}`. Substituting into `e_{2j+1}(U) + z·e_{2j}(U) = 0` and regrouping:
> ### `(ê_{2j+1} + zê_{2j}) + s(ê_{2j} + zê_{2j−1}) + p(ê_{2j−1} + zê_{2j−2}) = A_{2j+1} + s A_{2j} + p A_{2j−1} = 0`. ∎

> ### **The relations of `B`, seen from any pair of letters, ARE a three-term recursion.** *(Consistency: `j = 0` gives `A_1 = −s`, i.e. `ê_1 + z = −(a+b)`, i.e. `z = −e_1(U)`.)*

**Corollary.** Every odd `A` is divisible by `s`: `\;A_{2j+1} = −s·Σ_{i=0}^{j}(−p)^i A_{2j−2i}`. In particular `A_{2k−3} = −s·W` with `W := Σ_{i=0}^{k−2}(−p)^i A_{2k−4−2i}`.

---

# 3 · `THEOREM I` — THE COFACTOR *(`PROVED`, all `k ≥ 2`, all odd `q`; in `S'/E'_k`, no box)*

> ### `\;z^2·ε_{ab} = (a+b)·c_b`,  with  `\;c_b := (a+b)·A_{2k−2} + ab·\big(a+b−e_1(C')\big)·W`,  of degree `2k−1`.

**Proof.** From `e_{2k−2}(U) = ε_{ab} + p·ê_{2k−4}` and `e_{2k−1}(U) = −z·e_{2k−2}(U)`:
> ### `z·ε_{ab} = −e_{2k−1}(U) − z p ê_{2k−4} = −s ê_{2k−2} − p(ê_{2k−3} + zê_{2k−4}) = −s ê_{2k−2} − p·A_{2k−3}`.
Multiplying by `z` and using `LEMMA R` at `j = k−1` — which gives `z ê_{2k−2} = A_{2k−1} = −s A_{2k−2} − p A_{2k−3}`, since `ê_{2k−1} = 0`:
> ### `z^2 ε_{ab} = s^2 A_{2k−2} + s p A_{2k−3} − p z A_{2k−3} = s^2 A_{2k−2} + p(s−z)A_{2k−3}`.
🔴 **Here characteristic 3 enters, once:** `s − z = s + (s + ê_1) = 2s + ê_1 = −s + ê_1`.
Substituting `A_{2k−3} = −sW`:
> ### `z^2 ε_{ab} = s^2 A_{2k−2} + p s^2 W − p s ê_1 W = s·\big[s A_{2k−2} + p(s − ê_1)W\big] = s·c_b`. ∎

> ### **`q` does not appear anywhere in this statement or its proof: it lives in `S'/E'_k`, without the box.** *(At `k=2`, `W = 1` and `c_b = (a+b)(cd + z(c+d)) + ab(a+b−c−d)`.)*

---

# 4 · `LEMMA T` — A TWO-LETTER `LEMMA 0` *(`PROVED`, all `k`, all `q = 3^v`)*

> ### For **any** two letters `x, y` of the full alphabet `W`: `\;(Φ_x + Φ_y)·∏_{w∈W∖\{x,y\}} w = 0` in `B`.

**Proof.** Put `V' := W∖\{x,y\}` (`2k−1` letters), `e'_m := e_m(V')`, `ℓ := e_1(V')`, `μ := xy`, `D := e'_{2k−1} = ∏_{V'}w`. Since `e_1(W) = 0`, `x + y = −ℓ`, and the relations `e_{2j+1}(W) = 0` read
> ### `e'_{2j+1} − ℓ·e'_{2j} + μ·e'_{2j−1} = 0`,  `j = 0,…,k`.
At `j = k` this gives `μ·D = 0` (this is `LEMMA 0` in these letters). Multiplying the `j`-th relation by `ℓ^{q−1}`:
> ### `ℓ^{q−1}e'_{2j+1} = ℓ^{q}e'_{2j} − μ·ℓ^{q−1}e'_{2j−1} = −μ·ℓ^{q−1}e'_{2j−1}`,
🔴 **because `ℓ^q = e_1(V')^q = Σ_{v∈V'}v^q = 0` — characteristic 3 (Frobenius additivity) together with the box.** Descending from `j = k−1`:
> ### `ℓ^{q−1}D = (−μ)^{k−1}ℓ^{q−1}e'_1 = (−μ)^{k−1}ℓ^{q} = 0`.
Finally `(x+y)^{q−1}D = Σ_i \binom{q−1}{i}x^i y^{q−1−i}D`, and every term with `1 ≤ i ≤ q−2` contains `μD = 0`; only `i = 0` and `i = q−1` survive, giving `(Φ_x + Φ_y)D`. Since `q−1` is even, `(x+y)^{q−1} = (−ℓ)^{q−1} = ℓ^{q−1}`, hence
> ### `(Φ_x + Φ_y)D = ℓ^{q−1}D = 0`. ∎

> ### ⭐ **Compare: `LEMMA 0` reads `x·y·∏_{W∖\{x,y\}} = 0`; `LEMMA T` reads `(Φ_x + Φ_y)·∏_{W∖\{x,y\}} = 0`. The same shape, one floor up.**

---

# 5 · `THEOREM II` *(`PROVED`, all `k ≥ 1`, all `q = 3^v`)*

Write `V := U∖\{a\}`.
> ### `\;Σ_{b∈V} c_b·(Φ_a − Φ_b) = −Φ_a·e_{2k−1}(V)` in `B`.

**Two elementary identities** *(char-free; both verified symbolically)*:
> ### `(S1)` `\;Σ_{b∈V} b·e_m(V∖b) = (m+1)\,e_{m+1}(V)`  — each `(m+1)`-subset arises once per choice of `b` in it.
> ### `(S2)` `\;Σ_{b∈V} b^2·e_m(V∖b) = e_1(V)e_{m+1}(V) − (m+2)e_{m+2}(V)`.

**And the principle** `Φ_u·f = Φ_u·f|_{u=0}`, valid because `u·Φ_u = u^q = 0`.

**Step A — the coefficient of `Φ_a`.** Setting `a = 0` in `c_b` and summing with `(S1)`, `(S2)`:
> ### `Σ_b c_b|_{a=0} = (2k−1)e_{2k−1}(V) − (2k−2)e_1(V)e_{2k−2}(V)`.
Against `Φ_a`, using `Φ_a e_1(V) = −Φ_a z`, `Φ_a e_{2k−2}(V) = Φ_a e_{2k−2}(U)` and `−z\,e_{2k−2}(U) = e_{2k−1}(U)`, one gets `Φ_a e_1(V)e_{2k−2}(V) = Φ_a e_{2k−1}(V)`, hence
> ### `Φ_a·Σ_b c_b = Φ_a e_{2k−1}(V)·\big[(2k−1) − (2k−2)\big] = Φ_a·e_{2k−1}(V)`.

**Step B — the coefficients of `Φ_b`.** Setting `b = 0` and using `Φ_b(a + e_1(C')) = −Φ_b z`:
> ### `Σ_b Φ_b c_b = Σ_{b∈V} Φ_b·a·\big[e_{2k−2}(V) + z\,e_{2k−3}(V)\big]`.
**(B1)** `Σ_b Φ_b\,a\,e_{2k−2}(V) = Σ_b b^{q−2}e_{2k}(U) = (p_{q−2}(U) − a^{q−2})e_{2k}(U) = −a^{q−2}e_{2k}(U) = −Φ_a e_{2k−1}(V)`, using `LEMMA P` and `LEMMA 0`.
**(B2)** Writing `a\,e_{2k−3}(V) = e_{2k−2}(U) − e_{2k−2}(V)`, the two halves give `Φ_a e_{2k−1}(V)` and `−z^{q−1}e_{2k−1}(V)`, so
> ### `(B2) = (Φ_a + z^{q−1})·e_{2k−1}(V) = 0`  **by `LEMMA T` applied to the pair `\{a, z\}`**, since `∏_{W∖\{a,z\}} = e_{2k−1}(V)`.
Hence `Σ_b Φ_b c_b = −Φ_a e_{2k−1}(V)`, and
> ### `Σ_b c_b(Φ_a − Φ_b) = Φ_a e_{2k−1}(V) + Φ_a e_{2k−1}(V) = 2Φ_a e_{2k−1}(V) = −Φ_a e_{2k−1}(V)`.
🔴 **Characteristic 3 enters here, in the last line: `2 = −1`.** ∎

---

# 6 · `THEOREM STAR` *(`PROVED`, all `k ≥ 1`, all `q = 3^v`)*

> # `\;z^2σ_a = −Φ_a·e_{2k−1}(U∖a) = −a^{q−2}e_{2k}(U)`,  **and consequently**  `\;z^3σ_a = 0`.

**Proof.** Using `s_{ab} = h_{ab}ε_{ab}` and `(a+b)h_{ab} = Φ_a − Φ_b` — an identity in `S'`, requiring no expansion of `h_{ab}` into `q−1` terms:
> ### `z^2σ_a = Σ_b h_{ab}·z^2ε_{ab} \overset{\text{Thm I}}{=} Σ_b h_{ab}(a+b)c_b = Σ_b (Φ_a − Φ_b)c_b \overset{\text{Thm II}}{=} −Φ_a e_{2k−1}(V)`,
and `Φ_a e_{2k−1}(V) = a^{q−1}e_{2k−1}(U∖a) = a^{q−2}·a·e_{2k−1}(U∖a) = a^{q−2}e_{2k}(U)`. Multiplying once more by `z` and using `LEMMA 0` (`z·e_{2k}(U) = 0`):
> ### `z^3σ_a = −a^{q−2}·z\,e_{2k}(U) = 0`. ∎

> ### **Corollary.** Every star sum lies in `\operatorname{Ann}(z^3)`; and since the star span has dimension `2k−1` — from `σ_a = e_a ∧ v` with `v = (1,…,1)`, whose kernel is exactly `⟨v⟩` — the `⊇` half of the family statement follows.

---

# 7 · WHERE CHARACTERISTIC 3 IS CONSUMED — **three places, and only three**

| # | statement | step |
|---|---|---|
| **1** | `THEOREM I` | `s − z = 2s + ê_1 = −s + ê_1` |
| **2** | `LEMMA T` | `ℓ^q = Σ_{v} v^q = 0` *(Frobenius additivity + the box, `q = 3^v`)* |
| **3** | `THEOREM II` | the last line, `2·Φ_a e_{2k−1}(V) = −Φ_a e_{2k−1}(V)` |

> ### **`LEMMA R`, `LEMMA P`, the elementary identities `(S1)`, `(S2)` and Step A of `THEOREM II` are characteristic-free.** Nothing is claimed in characteristic `2`, nor for even `q`.

---

# 8 · GRADES, SCOPE, AND WHAT IS **NOT** CLAIMED

| statement | grade |
|---|---|
| `LEMMA R` | **PROVED**, all `k`, all `q`; no box, no characteristic |
| `THEOREM I` | **PROVED**, all `k ≥ 2`, all odd `q`; in `S'/E'_k`, **no `q` anywhere** |
| `LEMMA T` | **PROVED**, all `k`, all `q = 3^v` |
| `THEOREM II` | **PROVED**, all `k ≥ 1`, all `q = 3^v` |
| **`THEOREM STAR`** | **PROVED**, all `k ≥ 1`, all `q = 3^v` |
| Gates | **MEASURED** at `(2,9)` and `(3,9)`, with firing controls |

⚠️ **What is NOT claimed, stated so no reader can mistake it.**
> ### **(a)** These theorems describe **one family of generators** — the pairs `s_{ab}`. They say nothing about the families indexed by three, five, … letters.
> ### **(b)** They give the `⊇` half of the statement `\ker(z^3)|_{\text{span}\{s_{ab}\}} = \text{span}\{σ_a\}`. **The `⊆` half is MEASURED, not proved.**
> ### **(c)** The method generalises only in part: `THEOREM I` and the `Φ`-linearity are properties of the method, but `LEMMA R` is a three-term recursion **because the split has two letters** — for a split of `2t` letters it has `2t+1` terms — and the pair-shape of `LEMMA T` must be re-proved.

---
*Standalone `STAR IDENTITY v1` · Chaise Longue Campaign. Companion to `LDL-SHARP v1`, `CONJECTURE R v1`, `THEOREM OMEGA v1`, `JORDAN REDUCTION v2`, `SNAP THEOREMS v2` and `SXP-BOUND v1`.*
