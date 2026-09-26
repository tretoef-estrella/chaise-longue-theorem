> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Sofa campaign (Operación Glotón)* · 2026 (date not stated in the document)
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE T-BLOCK THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/THE_T_BLOCK_THEOREM.md
>
> **Status, as written in the document:** Status: pencil-proven for all v ≥ 2; pending the project's P0 program. Self-contained; the v=1 boundary is explicitly excluded (and handled by the sealed A(3) egg).
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v0`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE T-BLOCK THEOREM
## At the tower boundary, sheet identities split by large-exponent support, forcing Koszul antisymmetry

**Operación Glotón / The Sofa Theorem · standalone · English · Princeton rigor / Quanta clarity.**
**Status: pencil-proven for all v ≥ 2; pending the project's P0 program. Self-contained; the v=1 boundary is explicitly excluded (and handled by the sealed A(3) egg).**

---

### 0. Why this theorem matters (Quanta paragraph)
The Recognition Theorem tamed the *middle* of a Frobenius-tower problem by observing that below the threshold `q`, the large power `s_i^q` cannot interfere with itself: monomial supports stay disjoint and the tower drops out. But at the boundary — coefficient degrees `q ≤ e < q+4`, where the ideal `m^{[q]}` first bites — that disjointness begins to fail, and this is exactly where q-freeness genuinely breaks. The T-Block Theorem is the precise anatomy of that boundary: it shows the sheet identities still split into disjoint monomial *classes* (indexed by which coordinates carry a large exponent), and that the only surviving cross-terms are forced to be **antisymmetric** — the fingerprint of a Koszul syzygy `s_i^q s_j^q − s_j^q s_i^q`. The wall, up close, is made of Koszul relations with tiny cofactors.

### 1. Setup
`S = F₃[s₀..s₅]`, `E = (e₁,e₃,e₅) = ∩_J I_J` (the 15 matching-sheets of K₆). For a sheet `J` with pair coordinates `u₁,u₂,u₃` (via `s_b = −s_a` on each pair), a form restricts to `F₃[u₁,u₂,u₃]`. Fix `q = 3^v` and `f ∈ {0,1,2,3}`; consider `λ = (λ₀..λ₅)` homogeneous of degree `q+f` with `Σλᵢsᵢ^q ∈ E`, i.e. vanishing on every sheet.

On a sheet, set `Δ_k = (λ_{a_k} − λ_{b_k})|_{L_J}`, so the sheet identity is `Σ_{k=1}^3 Δ_k u_k^q = 0`. Since `deg Δ_k = q+f < 2q`, each monomial of `Δ_k` has **at most one** exponent `≥ q`; split canonically
`Δ_k = Δ_k^∅ + Σ_l u_l^q δ_{k,l}`, with `Δ_k^∅` the reduced part (all exponents `< q`) and `deg δ_{k,l} = f ≤ 3`.

### 2. The theorem
> **Theorem (T-Block).** Let `q ≥ 9` and `f ≤ 3`. Then the sheet identity `Σ_k Δ_k u_k^q = 0` forces, on every sheet:
> **(i)** `Δ_k^∅ = 0` for each `k` (the reduced part of every pair-difference vanishes);
> **(ii)** `δ_{k,k} = 0` (no deep-diagonal `u_k^{2q}` term);
> **(iii)** `δ_{l,k} = −δ_{k,l}` for `k ≠ l` (**Koszul antisymmetry**), with cofactor degree `f ≤ 3`.

### 3. Proof
Substitute the split into `Σ_k u_k^q Δ_k = 0`:
`Σ_k u_k^q Δ_k^∅ + Σ_{k,l} u_k^q u_l^q δ_{k,l} = 0`.
Index each monomial of the left side by its **set `T` of coordinates carrying an exponent `≥ q`**. Because the total degree is `2q+f < 3q` (using `q ≥ 9 > f`), no monomial can have three large exponents, so `|T| ≤ 2`. The three resulting classes are disjoint by exponent range:
- **`|T| = {k}` (one large exponent, in `[q, 2q−1]`):** contributed only by `u_k^q Δ_k^∅` (exponent of `u_k` is `q + (\text{that of }Δ_k^∅) < 2q`). Vanishing of this class ⟹ `Δ_k^∅ = 0` — (i).
- **`|T| = {k}` with the `u_k`-exponent `≥ 2q`:** contributed only by `u_k^q · u_k^q δ_{k,k} = u_k^{2q}δ_{k,k}`. Vanishing ⟹ `δ_{k,k} = 0` — (ii).
- **`|T| = {k,l}`, `k ≠ l`:** contributed only by `u_k^q u_l^q(δ_{k,l} + δ_{l,k})`. Vanishing ⟹ `δ_{k,l} + δ_{l,k} = 0` — (iii).
No class overlaps another (their large-exponent patterns differ), so each vanishes independently. ∎

### 4. The boundary case v = 1 (why q ≥ 9 is sharp)
At `q = 3`, the top collar degree gives total degree `2q+f = 6+f`, which can reach `3q = 9` when `f = 3`; then `|T| = 3` becomes possible and the class separation fails. This is not a defect but a genuine feature of the smallest level: `v = 1` is handled separately by the sealed direct computation `A(3) = 141 = P(3)`, and every statement here is quantified `v ≥ 2` (`q ≥ 9`), exactly matching the regime the tower argument needs.

### 5. What it buys (Quanta close)
The theorem reduces every boundary syzygy to: reduced parts obeying the *main-body* conditions (so they lie in the Recognition module `M`, of known q-free dimension), plus a package of **antisymmetric** cross-data `δ` of degree `≤ 3`. Antisymmetry is the signature of the Koszul syzygies `s_i^q s_j^q = s_j^q s_i^q`; the remaining work (bounding how much such data can appear) becomes a *fixed*, finite linear-algebra problem — the collar rank certificate. The tower wall, resolved at the boundary, is Koszul all the way down.

*The anatomy of the boundary. — Constructor "Bisel".*
