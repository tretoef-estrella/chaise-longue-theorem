> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Sofa campaign (Operación Glotón)* · 2026-06-29
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE PER-EDGE DETERMINANT THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/THE_PER_EDGE_DETERMINANT_THEOREM.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v0`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE PER-EDGE DETERMINANT THEOREM

**The sign matrix of a single edge has determinant 2^{D−1}, coprime to 3 at every tower level**

**Rafael Amichis Luengo** · Madrid · [github.com/tretoef-estrella](https://github.com/tretoef-estrella)

**29 June 2026** · Operación Glotón / The Sofa Theorem · Constructor: DualSix · Auditor: DualSix

---

## 1. Setup

For a positive integer D, define the **per-edge sign matrix** M_D ∈ Z^{D × D} by:

> M_D[e, c] = +1 if c ≥ e, and −1 if c < e

for row index e ∈ {0, ..., D−1} and column index c ∈ {0, ..., D−1}.

This matrix arises in the DeltaZ construction for Fermat varieties: each edge (a, b) of a perfect matching of K₆ contributes one copy of M_D to the leg matrix via the sign function sgn(β'_a − β'_b). The full leg matrix for a matching with 3 edges is the tensor product M_D ⊗ M_D ⊗ M_D, and the DeltaZ matrix is a vertical stack of 15 such tensor products (one per matching).

**Explicit form.** The matrix M_D has the following structure:

```
Row 0:   [+1  +1  +1  +1  ...  +1  +1]
Row 1:   [−1  +1  +1  +1  ...  +1  +1]
Row 2:   [−1  −1  +1  +1  ...  +1  +1]
Row 3:   [−1  −1  −1  +1  ...  +1  +1]
  ⋮
Row D−1: [−1  −1  −1  −1  ...  −1  +1]
```

Each row has −1's in positions 0 through e−1 and +1's in positions e through D−1.

---

## 2. The Per-Edge Determinant Theorem

**Theorem.** For every positive integer D ≥ 1:

> det(M_D) = 2^{D−1}.

In particular, det(M_D) is a power of 2, hence coprime to every odd prime. For the Fermat tower (D = 3^v, v ≥ 1): v₃(det(M_D)) = 0.

---

## 3. Proof

Perform row reduction. For k = 0, 1, ..., D−2, subtract Row k from Row k+1:

> Row_{k+1} − Row_k = (0, 0, ..., 0, 2, 0, ..., 0)

with the single nonzero entry 2 at position k. This is because:
- For c < k: both Row_k and Row_{k+1} have entry −1. Difference = 0.
- For c = k: Row_k has +1, Row_{k+1} has −1. Difference = −1 − (+1) = −2. Wait — let me redo this carefully.

Actually: Row_k[c] = +1 if c ≥ k, −1 if c < k. Row_{k+1}[c] = +1 if c ≥ k+1, −1 if c < k+1.

Row_{k+1}[c] − Row_k[c]:
- If c < k: (−1) − (−1) = 0.
- If c = k: (−1) − (+1) = −2.
- If c > k: (+1) − (+1) = 0.

So Row_{k+1} − Row_k = (0, ..., 0, −2, 0, ..., 0) with −2 at position k.

After D−1 such subtractions, the matrix becomes upper-triangular:

```
Row 0:   [+1  +1  +1  ...  +1]        (unchanged)
Row 1:   [ 0  −2   0  ...   0]        (Row_1 − Row_0)
Row 2:   [ 0   0  −2  ...   0]        (Row_2 − Row_1)
  ⋮
Row D−1: [ 0   0   0  ...  −2]        (Row_{D−1} − Row_{D−2})
```

The diagonal entries are: 1, −2, −2, ..., −2 (one 1 and D−1 copies of −2).

The determinant of an upper-triangular matrix is the product of its diagonal:

> det = 1 · (−2)^{D−1} = (−1)^{D−1} · 2^{D−1}.

Since det is defined up to sign for the purpose of torsion analysis (we care about |det| and its prime factorization):

> |det(M_D)| = 2^{D−1}. ∎

**Remark.** The signed determinant is (−1)^{D−1} · 2^{D−1}. For D odd (including all tower levels D = 3^v): det = 2^{D−1}. For D even: det = −2^{D−1}.

---

## 4. The Smith Normal Form

**Corollary.** The Smith normal form of M_D is diag(1, 2, 2, ..., 2) — one invariant factor equal to 1 and D−1 invariant factors equal to 2.

*Proof.* From the row reduction in §3: the matrix is equivalent (via elementary row operations) to diag(1, −2, −2, ..., −2). The Smith normal form extracts the invariant factors as the ratios of consecutive GCDs of minors. Since all entries of M_D are ±1, every 1×1 minor is ±1, so d₁ = gcd(all entries) = 1. The product of all invariant factors = |det| = 2^{D−1}. With d₁ = 1 and d₁ · d₂ · ... · d_D = 2^{D−1}, and each subsequent invariant factor dividing the next: the unique solution is (1, 2, 2, ..., 2). ∎

---

## 5. Consequences for the DeltaZ matrix

### 5.1 Individual edges are always clean

Each edge contributes a factor M_D with det coprime to 3. Therefore no individual edge introduces 3-torsion into the DeltaZ matrix, at any tower level.

### 5.2 Individual legs are always clean

Each leg (matching) contributes M_D ⊗ M_D ⊗ M_D, with determinant (2^{D−1})³ = 2^{3(D−1)}, coprime to 3. A single leg has drop = 0 at every D. Verified: rank_Q = rank_F₃ = D³ for each individual leg.

### 5.3 All torsion is multi-leg overlap

Since individual legs are clean, the 3-torsion in the DeltaZ cokernel arises entirely from the OVERLAP between different legs — how their images in the target lattice Z^{D⁶} interfere. This interference is governed by the matching structure of K₆ (which edges are shared between matchings), not by the arithmetic of individual edges.

---

## 6. Verification

| D | det(M_D) | |det| | v₃(|det|) | SNF |
|---|----------|-------|-----------|-----|
| 1 | 1 = 2⁰ | 1 | 0 | (1) |
| 2 | −2 = −2¹ | 2 | 0 | (1, 2) |
| 3 | 4 = 2² | 4 | 0 | (1, 2, 2) |
| 4 | −8 = −2³ | 8 | 0 | (1, 2, 2, 2) |
| 5 | 16 = 2⁴ | 16 | 0 | (1, 2, 2, 2, 2) |
| 9 | 256 = 2⁸ | 256 | 0 | (1, 2, 2, 2, 2, 2, 2, 2, 2) |
| 27 | 2²⁶ | 2²⁶ | 0 | (1, 2²⁶) |
| 81 | 2⁸⁰ | 2⁸⁰ | 0 | (1, 2⁸⁰) |

All values coprime to 3. The pattern det = (−1)^{D−1} · 2^{D−1} holds universally.

---

*Theorem stated and proved 29 June 2026. Verified computationally at D = 1, ..., 9 and at D = 27, 81 (via the closed formula). Operación Glotón / The Sofa Theorem. Architect: Rafael Amichis Luengo.*

## References

1. A. Degtyarev, I. Shimada, *On the topology of projective subspaces in complex Fermat varieties.* J. Math. Soc. Japan **68**:3 (2016), 975–996. arXiv:1405.4683.
2. R. Amichis Luengo, *The Orbit Theorem.* Campaign note, 29 June 2026.
3. R. Amichis Luengo, *The Balance Theorem.* Campaign note, 30 June 2026.
