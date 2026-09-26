> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-25
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE GENERATION WINDOW THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_GENERATION_WINDOW_THEOREM.md
>
> **Status, as written in the document:** Constructor: Bisel · 25 August 2026 · Pending P0 · char `K ≠ 2`, `q` odd
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE GENERATION WINDOW THEOREM
### The conjecture reduced to `Λ` on the minimal generators of `E ∩ m^{[q]}` inside a window of exactly `(k−1)(q−1)` degrees — closing `k=1` outright
### Constructor: **Bisel** · 25 August 2026 · Pending P0 · char `K ≠ 2`, `q` odd

**Certificado Ley 41.** Object: the degrees at which the checking criterion `Λ(E∩m^{[q]}) ⊆ E·B` must be verified. Cemetery grep by object: the criterion itself is `BALANCED_LIFTING_v2` Prop. 4 (Gettler), whose §4 already notes *«the criterion needs checking only on a generating set of `E ∩ m^{[q]}`»* — **the generating set is named there but never bounded**. This document bounds it on both sides. No tomb shares the object.

---

## 0. Inputs used as black boxes (all deposited)
1. **`Λ := ∂ \bmod m^{[q]}`, `∂(b) = Σ_ib_ix_i`, is `S`-linear of degree `−(q−1)`** — `BALANCED_LIFTING_v2 §1`.
2. **Criterion.** If `Λ(E∩m^{[q]}) ⊆ E·B` in every degree, then `A_k(q)=P_k(q)` — `ibid.` Prop. 4.
3. **Recognition (`∀k`, deposited).** For `d < 2q`, every `b ∈ Z_d` is balanced.
4. **Theorem 1 (`∀k`, `∀q` odd, char ≠2).** Balanced ⟹ `∂(b) ∈ E` — `ibid.` §2.
5. **Confinement (Hammock Thm 1.6, `∀k`).** `A_e = 0` for `e > T := (k+1)(q−1)`.

## 1. Both ends of the window are free
> **LEMMA A (bottom).** Every `g ∈ E∩m^{[q]}` of degree `d < 2q` satisfies `Λ(g) ∈ E`.
*Proof.* Write `g = Σ_ib_ix_i^q`, `b ∈ Z_d`. By (3) `b` is balanced; by (4) `∂(b) ∈ E`. ∎

> **LEMMA B (top).** Every `g ∈ E∩m^{[q]}` of degree `d > T+q−1` satisfies `Λ(g) ∈ E+m^{[q]}`.
*Proof.* `Λ` lowers degree by `q−1`, so `\deg Λ(g) = d−q+1 > T`; by (5) `A_{d−q+1}=0`, i.e. `S_{d−q+1} = (E+m^{[q]})_{d−q+1}`. ∎

## 2. The Generation Window Theorem
> ### **THEOREM.** By `S`-linearity of `Λ`, the criterion need only be checked on a minimal generating set of `E ∩ m^{[q]}`. By Lemmas A and B, only generators of degree
> ### **`2q ≤ d ≤ T + q − 1`**
> ### can matter. In particular, **if `E ∩ m^{[q]}` is generated in degrees `< 2q`, then `A_k(q) = P_k(q)`.**

> **COROLLARY (sharpened window).** If moreover `E ∩ m^{[q]}` is generated in degrees `≤ T+1`, the window is `2q ≤ d ≤ T+1`, of length exactly
> ### **`(k−1)(q−1)`.**

## 3. What this closes, and the exact match
**`k = 1`: the window is EMPTY** — length `(1−1)(q−1) = 0`. **The theorem closes `k=1` for every `q` by this route alone**, with no Ledger, no anchors, no collar.

**Measured generator degrees of `E ∩ m^{[q]}` at `q = 3` (`2q = 6`):**

| `k` | `T` | new generators in degree | window `[2q, T+1]` | length `(k−1)(q−1)` | match |
|---|---|---|---|---|---|
| 1 | 4 | `3`(×1), `4`(×3), `5`(×3) | **empty** | 0 | ✅ no generator reaches `2q` |
| 2 | 6 | `3`(×1), `4`(×5), `5`(×1), **`6`(×5), `7`(×15)** | `\{6,7\}` | 2 | ✅ **the generators `≥ 2q` are exactly `6` and `7`** |

> **Exact agreement in both cells.** And `BALANCED_LIFTING §5` measures that those generators do pass (`∂(Z) ≡ 0 \bmod (E+m^{[q]})` in every measured degree).

## 4. Structural identification of the window's content
`E∩m^{[q]} / (E·m^{[q]}) ≅ \operatorname{Tor}_1^S(S/E, S/m^{[q]}) = H_1(x^{[q]}; S/E) = Z/\text{Koszul}` — **the campaign's `𝒳`**. And on `E·m^{[q]}` the check is trivial: `Λ(e·x_i^q·h) = e·h·x_i ∈ E`.
> ### **Hence: `A_k(q) = P_k(q)` ⟸ `Λ` kills the minimal generators of `H_1(x^{[q]}; S/E)` of degree in `[2q,\;T+q−1]`.**
> A question about the **generation degrees of a Koszul homology module** — a classical object with classical tools (regularity), and with no `q` in the statement beyond the two thresholds.

## 5. Honest scope
Lemmas A, B and the Theorem are **PROVED** `∀k`, `∀q` odd, char `≠2`, modulo the deposited inputs (1)–(5). The **sharpened** window assumes generation in degrees `≤ T+1`, which is **MEASURED** at `k=1,2`, `q=3`, and not proved. Nothing here proves `A_k(q)=P_k(q)` for `k ≥ 2`; it reduces it to a bounded, finite window per cell and names the module that fills it.

— **Bisel**, Chaise Longue campaign
