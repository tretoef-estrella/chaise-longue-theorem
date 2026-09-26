> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Sofa campaign (Operación Glotón)* · 2026-06-30
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE BALANCE THEOREM — CORRECTED (v2)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/THE_BALANCE_THEOREM.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (3 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v2`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE BALANCE THEOREM — CORRECTED (v2)

**The full set of 15 matchings is the unique subset of K₆ with perfect mod-3 edge balance**

**Rafael Amichis Luengo** · Madrid · [github.com/tretoef-estrella](https://github.com/tretoef-estrella)

**Original: 30 June 2026 · Correction: 1 July 2026** · Operación Glotón / The Sofa Theorem
Correction by: Bugs Bunny (Constructor) · Confirmed byte-exact by: Blas (Auditor)

---

> **CORRECTION NOTICE (1 July 2026).** The original §3 (Step 2) stated three numbers that are
> byte-exact wrong: rank_ℚ(A) = 15, rank_F₃(A) = 14, and the eigenvalues of AᵀA as {9(×1),
> 1(×5), 4(×9)}. The measured truth is **rank_ℚ(A) = 10, rank_F₃(A) = 10, eigenvalues {9(×1),
> 0(×5), 4(×9)}**. The single root error was recording the multiplicity-5 eigenvalue as 1 instead
> of 0. Consequently the published mechanism — "rank 15 → the 9 collapses mod 3 → rank 14 →
> kernel dimension 1" — is false. **The THEOREM'S CONCLUSION SURVIVES** (the full set is the
> unique mod-3-balanced subset), but by a finer, verified reason given below. §3 is rewritten;
> §§1–2, 4, 5 stand. Confirmed independently by both Constructor and Auditor, three tools each
> (sympy rank, numpy eigvalsh, sympy Smith normal form), plus brute-force enumeration.

---

## 1. Setup

Let K₆ denote the complete graph on vertex set V = {0, 1, 2, 3, 4, 5}. It has |E(K₆)| = 15 edges.
A **perfect matching** of K₆ is a set of 3 disjoint edges that partition V. There are exactly 15
perfect matchings, denoted J₀, ..., J₁₄.

For each edge e ∈ E(K₆) and each subset S ⊆ {0, ..., 14} of matchings, define the **multiplicity**:

> m_e(S) = |{j ∈ S : e ∈ J_j}|

This counts how many matchings in S contain edge e.

---

## 2. The key count

**Lemma.** Each edge e ∈ E(K₆) is contained in exactly 3 of the 15 matchings.

*Proof.* Fix an edge e = {a, b}. The remaining 4 vertices {c, d, f, g} = V \ {a, b} must be
partitioned into 2 disjoint edges. The number of perfect matchings of K₄ on 4 vertices is 3.
Each such pairing, combined with the fixed edge {a, b}, gives a matching of K₆. Therefore
m_e({0,...,14}) = 3 for every edge e. ∎

**Corollary.** The total edge-weight of the full set is Σ_e m_e({0,...,14}) = 15 · 3 = 45.
Cross-check: 15 matchings × 3 edges = 45. ✓

**Byte-exact confirmation.** The edge-membership matrix A ∈ {0,1}^{15×15} (rows = edges,
columns = matchings) has every row sum = 3 and every column sum = 3. Verified.

---

## 3. The Balance Theorem — CORRECTED PROOF

**Definition.** A subset S ⊆ {0, ..., 14} has **perfect mod-3 balance** if m_e(S) ≡ 0 (mod 3)
for every edge e ∈ E(K₆).

**Theorem (Balance Theorem).** The full set S = {0, 1, ..., 14} is the unique nonempty subset of
matchings with perfect mod-3 balance.

The balance condition is A · χ_S ≡ 0 (mod 3), where A_{e,j} = 1 iff edge e ∈ matching J_j, and
χ_S ∈ F₃^{15} is the characteristic vector of S.

### 3.1 The measured invariants of A (byte-exact, three independent tools)

| Quantity | Original §3 claim | Measured truth |
|---|---|---|
| eigenvalues of AᵀA | 9(×1), **1(×5)**, 4(×9) | 9(×1), **0(×5)**, 4(×9) |
| rank_ℚ(A) | 15 | **10** |
| rank_F₃(A) | 14 | **10** |
| Smith normal form of A | (not given) | **diag(1,1,1,1,1,1,1,1,1,1, 0,0,0,0,0)** |
| dim ker(A) (right null) | 1 | **5** (identical over ℚ and F₃) |

Three consequences follow, and they replace the entire original mechanism:

1. **No mod-3 rank collapse.** rank_ℚ(A) = rank_F₃(A) = 10. Passing from ℚ to F₃ drops nothing.
   The five zero-eigenvalues of AᵀA are honest rational dependencies (right-kernel of dimension 5
   over ℚ), *not* a modular phenomenon. The original "9 ≡ 0 mod 3 collapses one mode" does not
   occur: the zero modes are already zero over ℚ.

2. **A carries no factor of 3.** The Smith normal form of A has elementary divisors all equal to
   1 (ten of them) and the rest 0. **Every invariant factor is coprime to 3.** A is 3-adically
   clean.

3. **The kernel is 5-dimensional, identical over ℚ and F₃, and contains the all-ones vector.**
   A · (1,...,1)ᵀ = (3,...,3)ᵀ ≡ 0 (mod 3) (each edge in exactly 3 matchings, by the Lemma).

### 3.2 Uniqueness of the balanced subset (the corrected argument)

The original claim "ker(A) = span{all-ones}" is **false**: ker(A) has dimension 5. Uniqueness
does not come from the kernel being a line. It comes from a counting fact, verified by exhaustive
enumeration:

**Proposition (Unique {0,1}-vector in the kernel).** Of the 3⁵ = 243 vectors in ker_{F₃}(A),
**exactly one** has all coordinates in {0, 1} ⊂ F₃ and is nonzero: the all-ones vector, i.e. the
full set.

*Proof.* Exhaustive check over all 2^{15} − 1 = 32,767 nonzero {0,1}^{15} vectors χ: the
condition A · χ ≡ 0 (mod 3) holds for **exactly one**, namely χ = (1,…,1), of weight 15. (Engine
cross-check consistent; here reproduced in seconds in-sandbox.) ∎

A nonempty subset S has perfect mod-3 balance iff χ_S ∈ ker_{F₃}(A) and χ_S ∈ {0,1}^{15}. By the
Proposition, the only such vector is the all-ones, so S = {0,…,14}. ∎

> **Why the corrected statement is STRONGER, not weaker.** The original proof would have made
> uniqueness a triviality (a 1-dim kernel with one {0,1} vector). The truth is subtler: the kernel
> is 5-dimensional (243 vectors over F₃), and yet the {0,1} cube meets it in a single point. The
> full set is distinguished not by the kernel being small, but by being the sole Boolean
> configuration in a large kernel. This is a genuine feature of the fixed graph K₆, v-independent.

---

## 4. Computational verification

Exhaustive enumeration over all 32,766 nonempty subsets S: only S = {0,...,14} satisfies mod-3
balance. Zero exceptions. Independently confirmed by the kernel/Smith computation of A over ℚ and
F₃ (rank 10 both, Smith all-1/0, right-kernel dimension 5, all-ones inside), byte-exact, by
Constructor (Bugs Bunny) and Auditor (Blas).

---

## 5. Connection to the 3·Δ identity — and the 3-adic consequence

The Balance Theorem underlies the algebraic identity

> 3 · Δ_full = Σ_{e ∈ E(K₆)} E_e,   E_e = Σ_{j : e ∈ J_j} Δ_{J_j},

with each E_e torsion-free (det E_e = 2^{D−1}, coprime to 3). The factor 3 arises because each
leg appears once per edge, i.e. 3 times.

**New 3-adic consequence (from the corrected §3).** Because the Smith normal form of the
edge-incidence A has every invariant factor coprime to 3, **A contributes no factor of 3 to the
torsion of the assembly, at any tower level v** (A is the incidence of the *fixed* graph K₆; its
Smith form does not depend on D). Therefore:

> Any 3-torsion in coker Δ cannot originate in the flat 0/1 edge-incidence structure. It must
> reside entirely in the signed/exponent data of the legs.

This retires, with data, any route that attributes the torsion's factor of 3 to a mod-3 rank
collapse of the edge-incidence matrix: **no such collapse exists.** It converges with the
independent cemetery autopsy (Blas): the seven distinct dead blind-objects are all degree-≤2
(edge/pair/incidence) and are blind for the same reason A is 3-clean — the torsion lives one floor
up, in the degree-3 signed overlap, not in the flat incidence.

---

*Corrected 1 July 2026. The conclusion of the Balance Theorem stands; its §3 proof is replaced.
The edge-incidence matrix A of K₆ has rank_ℚ = rank_F₃ = 10, Smith normal form all-1/0 (no factor
of 3), right-kernel dimension 5 (identical over ℚ and F₃), and the all-ones vector is the unique
{0,1} vector in that kernel — hence the full set is the unique mod-3-balanced subset. A is
3-adically clean at every tower level, so the torsion's factor of 3 cannot arise from the flat
edge-incidence. Byte-exact, three tools, cross-confirmed by Constructor and Auditor. Operación
Glotón / The Sofa Theorem. Architect: Rafael Amichis Luengo.*

### References
1. A. Degtyarev, I. Shimada, arXiv:1405.4683.
2. R. Amichis Luengo, Per-Edge Determinant / Forced Rank / Orbit / Exponent Bound Theorems.
3. Bugs Bunny → Blas communiqué (1 July 2026): the §3 crack and its confirmation.
