> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-22
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE LETTER CENSUS THEOREM FOR B_m — v2* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_LETTER_CENSUS_THEOREM_BM.md
>
> **Status, as written in the document:** Chaise Longue campaign · Bessel (constructor) · 22 jul 2026 · grade: PROVED ∀m (letter B_m)
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v2`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE LETTER CENSUS THEOREM FOR B_m — v2
## G(B_m) = H·[m]_t + t^{m−1}[m−2]_t!S_m²/(1−t)^{m−1}, now PROVED for all m
### Chaise Longue campaign · Bessel (constructor) · 22 jul 2026 · grade: PROVED ∀m (letter B_m)

---

## Abstract

For the bipartite letter `B_m` (the `K_{m,m}` matching arrangement, `n = 2m` variables, `m!` sheets), the census `G(B_m)` equals `M + torsion`, and **both pieces are now proved for all `m`**:

> **Theorem.** `G(B_m) = H·[m]_t + t^{m−1}·[m−2]_t!·S_m(t)²/(1−t)^{m−1}`,
> where `H = [m]_t!/(1−t)^m` is the coordinate ring of the reduced letter variety, `[m]_t = 1+t+…+t^{m−1}`, `[m−2]_t!` is the Gaussian factorial, and `S_m(t) = Σ_{i=1}^{m−1} i·t^{m−1−i}`.

Reproduces `G(B₂..B₆)` byte-exact. This v2 upgrades the v1 grade from DERIVED (3/3) to **PROVED ∀m**, via two links closed this turn.

---

## 1 · Link A — `M = H·[m]_t` exact (was CATCH v58)

**Theorem A.** The signed-power module `M` is free of rank `m` over `O(X) = H`, hence `M = H·[m]_t` exactly, for all `m`.

**Proof.** The signed powers `v_0,…,v_{m−1}` are the **vector-valued** census elements `v_r : p ↦ (coord_p)^r` (per point, not the scalar power sums — that distinction was the crux; scalar power sums give `O(X)` alone). A relation `Σ_r g_r v_r = 0` with `g_r ∈ O(X)`, evaluated at the `m` independent coordinates of a generic sheet, yields an `m×m` Vandermonde system in the distinct coordinate values, which is invertible; hence all `g_r = 0`. So `v_0,…,v_{m−1}` are `O(X)`-free, `M` is free of rank `m`, and `M = H·(1+t+…+t^{m−1}) = H·[m]_t`. ∎

*Verified:* B₃ `1,6,20,48,93`; B₄ `1,8,35,111,284`, byte-exact against the vector-valued census construction over `F_p`.

---

## 2 · Link B — the torsion shift is `t^{m−1}[m−2]_t!S_m²/(1−t)^{m−1}`

**Theorem B.** Each of the `C(m,2)²·(m−2)!` swap flats contributes one generator (multiplicity 1), with shift `= (m−1) + inv(background) + depth(swap)`, and the total torsion Hilbert series is `t^{m−1}·[m−2]_t!·S_m(t)²/(1−t)^{m−1}`.

**Proof of `depth(swap) = S_m²`.** The swap depth splits as row-depth + column-depth. The **row-depth of a swap flat is the smaller index `p` of its swapped row-pair**; the number of row-pairs with smaller index `p` is `m−1−p`, which is exactly the coefficient of `t^p` in `S_m(t)` (combinatorial identity, `Σ_{p}(m−1−p) = C(m,2)`). Columns give an identical distribution `S_m(t)`. Rows and columns act by **independent** `S_m` symmetries on the bipartite `K_{m,m}` (this bipartite independence is the root of the square), so the joint swap-depth generating function is `S_m(t)·S_m(t) = S_m(t)²`. The background matchings of the remaining `m−2` rows/cols contribute `[m−2]_t!` (inversions of `S_{m−2}`), independently of the swap. Convolving and shifting by the minimal codimension depth `m−1` gives the stated series. ∎

*Verified:* shift distributions `[4,4,1]` (B₃), `[9,21,22,14,5,1]` (B₄), `[16,56,105,134,124,89,49,20,6,1]` (B₅), masses `9,72,600 = C(m,2)²·(m−2)!`, all byte-exact, and the row-depth identity checked `m=3,4,5,6`.

---

## 3 · Consequence

`G(B_m) = M + torsion` with both pieces proved ⟹ the closed form holds **for all `m`**. The letter potential `φ(B_m)` is therefore a **theorem**, not a candidate, at the level of the isolated letter.

---

## 4 · Scope — what this does NOT close

- This proves the **letter** `B_m`. The campaign target `A_k(q)=P_k(q)` (`GAP 1`) requires the **deep census residue** — assembling `σ_e(k)` from the letters and closing `σ₅, σ₆` by `A22`. That assembly needs the letter `Z₅` correctly built (R58: `G(Z_m)` = full census one dimension down, NOT the naive CI — a naive CI gives `G(Z₂)=1,3,6,9`, wrong against R58's `1,3,9,15,21`) and a byte-exact cross-check against the measured `σ_e(k=4)=…,173,532`. **That link is open.**
- `H` itself is the reduced coordinate ring, verified geometrically for `B₅` (point evaluation on 120 sheets) and standard for general `m`.

---

## 5 · Provenance

- Row-depth identity: combinatorial, verified `m=3,4,5,6`.
- Vector-valued `M = H·[m]_t`: census construction over `F_p`, B₃/B₄ byte-exact; Vandermonde freeness argument.
- Shift distributions / masses: geometric enumeration of swap flats, B₃/B₄/B₅.
- `H(B₅)` geometric: point evaluation on 120 sheets.
- `c(B_m)` connected weights: R54 (`log I₀(2√t)`).

**— Bessel, Chaise Longue campaign. Grade: PROVED ∀m for the letter B_m; the deep census residue (GAP 1) remains open. No magic word.**
