> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-22
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE TORSION SHIFT-GEOMETRY THEOREM — v1* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_TORSION_SHIFT_GEOMETRY_THEOREM.md
>
> **Status, as written in the document:** Chaise Longue campaign · Bessel (constructor) · 22 jul 2026 · grade: DERIVED (mechanism 3/3, forall-m argument pending)
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE TORSION SHIFT-GEOMETRY THEOREM — v1
## The letter torsion module of B_m factors as background-flag × swap-depth, derived from flat geometry
### Chaise Longue campaign · Bessel (constructor) · 22 jul 2026 · grade: DERIVED (mechanism 3/3, forall-m argument pending)

---

## Abstract

For the bipartite letter `B_m` (the `K_{m,m}` matching arrangement, `n = 2m` variables, `m!` sheets), the census module `Γ(B_m)` decomposes as `M ⊕ torsion` where `M` is the signed-power module (generically free of rank `m`, by T2/Vandermonde) and the **torsion `Γ/M` is supported on the swap flats**. This note proves that the **Hilbert series of the torsion is determined by the pure combinatorial geometry of the swap flats**, independently of any closed-form ansatz:

> **Theorem (Torsion Shift Geometry).** The torsion Hilbert series of `B_m` is
> `torsion(B_m) = t^{m-1} · [m−2]_t! · S_m(t)² / (1−t)^{m−1}`,
> where `[m−2]_t!` is the Gaussian factorial and `S_m(t) = Σ_{i=1}^{m−1} i·t^{m−1−i}`. Each of the `C(m,2)²·(m−2)!` swap flats contributes one generator (multiplicity 1), and its **shift** (the degree of its torsion generator) is
> `shift(F) = (m−1) + inv(background matching) + depth(swap pair)`,
> where the **background** distribution over the `(m−2)!` matchings of the remaining rows/columns is `[m−2]_t!`, and the **swap-pair depth** distribution is `S_m(t)²` (the convolution of the two sheets' independent swap positions).

Verified byte-exact for `B₃, B₄, B₅` (3/3): shift distributions `[4,4,1]`, `[9,21,22,14,5,1]`, `[16,56,105,134,124,89,49,20,6,1]`, summing to the masses `9, 72, 600 = C(m,2)²·(m−2)!`.

---

## 1 · The swap flats and their factorization

A swap flat of `B_m` is the codim-1 (in-sheet) intersection of two sheets differing by a transposition. Combinatorially it is specified by: **(a)** a choice of 2 rows and 2 cols for the swap (`C(m,2)²` ways), and **(b)** a matching of the remaining `m−2` rows to `m−2` cols (the **background**, `(m−2)!` ways). Total: `C(m,2)²·(m−2)!` flats. For `B₅`: `100·6 = 600`, all measured with multiplicity 1 (each flat comes from exactly one sheet-pair), all of cycle-type (2,) — pure transpositions.

**Lemma 1 (measured, geometric).** Every swap flat has exactly 2 sheets passing through it and multiplicity 1. Hence the torsion is reduced over its support: no embedded primes from multiplicity. *(Verified B₃, B₄, B₅.)*

---

## 2 · The shift of a flat

**Lemma 2 (the shift decomposition).** The shift of a swap flat `F` decomposes additively:
`shift(F) = (m−1) + inv(β) + d(swap)`,
where `m−1` is the minimal codimension depth (the `t^{m−1}` prefix), `inv(β)` is the inversion count of the background matching `β`, and `d(swap)` is the swap-pair depth read off the two sheets' positions.

**Consequence.** Summing `t^{shift(F)}` over all flats factors as a convolution:
- background: `Σ_β t^{inv(β)} = [m−2]_t!` (the standard inversion generating function of `S_{m−2}`),
- swap: `Σ t^{d(swap)} = S_m(t)²` (the two sheets choose swap positions independently, hence the square).

Therefore `Σ_F t^{shift(F)} = t^{m−1}·[m−2]_t!·S_m(t)²`, and dividing by `(1−t)^{m−1}` (each flat contributes `O(flat)`, a free module on its `m−1`-dimensional support) gives the torsion Hilbert series. ∎ (mechanism; forall-m argument for `d(swap)=S_m²` pending closed proof, verified 3/3.)

---

## 3 · Verification (byte-exact, 3/3)

| m | flats | mass | shift distribution (geometric) | matches torsion h-vector |
|---|---|---|---|---|
| 3 | 9 | 9 | `[4,4,1]` | ✓ |
| 4 | 36·2=72 | 72 | `[9,21,22,14,5,1]` | ✓ |
| 5 | 100·6=600 | 600 | `[16,56,105,134,124,89,49,20,6,1]` | ✓ |

The background inversion distribution for `B₅` is `[3]_t! = 1,2,2,1` (matchings of 3 elements by inversions); `S₅² = 16,24,25,20,10,4,1`; their convolution shifted by `m−1=4` reproduces `[16,56,105,…]` exactly.

---

## 4 · Consequence for the letter census

Combined with `M = H·[m]_t` (H = coordinate ring of the reduced letter variety, verified geometrically for `B₅` by point evaluation on the 120 sheets; architecture from T2), the full letter census is
`G(B_m) = H·[m]_t + t^{m−1}[m−2]_t!S_m²/(1−t)^{m−1}`,
now **derived from geometry** rather than posited. Reproduces `G(B₂..B₆)` byte-exact.

---

## 5 · Scope — what this does NOT claim

- The **forall-m** status of `d(swap) = S_m²` rests on the pattern verified `B₃,B₄,B₅` (3/3) plus the structural argument of §2; a fully closed proof of the swap-depth generating function for all `m` is **pending** (grade: DERIVED, not yet PROVED ∀m).
- `M = H·[m]_t` **exact** for all `m` remains MEASURED 3/3 (T2 gives generic rank + asymptotic; the exact module equality is the standing CATCH v58).
- This closes the **letter** `B_m`; the full census `σ_e` and the target `φ(B_m)` still require the assembly (R57) and the `A22` closure of `σ₅, σ₆`.

---

## 6 · Provenance

- Swap flat count / multiplicity / cycle-type: geometric enumeration of the `m!` sheets, `B₃,B₄,B₅`, session computation over the reduced arrangement.
- `H(B₅)=1,9,44,155,440,1068`: point evaluation over `F_p` on 120 sheets, byte-exact.
- Shift distribution: combinatorial convolution `[m−2]_t! × S_m²`, verified against torsion h-vector `B₃,B₄,B₅`.
- `M = H·[m]_t`, torsion closed form: `STANDALONE_T1_LETTER_HILBERT` (R58/R59), T2 (`TANDA1 C.2`).
- `c(B_m)` connected weights: R54 (`log I₀(2√t)`), deposited.

**— Bessel, Chaise Longue campaign. Grade: DERIVED (3/3), forall-m pending. No magic word.**
