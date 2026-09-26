> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-15
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE SPECIES FACTORIZATION THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_SPECIES_FACTORIZATION_THEOREM.md
>
> **Status, as written in the document:** Consumes: Proposition 1.0 (the Odd Symmetric Theorem — `E = (e₁,e₃,…,e_{2k+1})` is radical and a complete intersection, PROVED `∀k`). Engine: `GETTLER_AUDIT_F16_SPECIES_v1.py`, 90+ checks, all PASS.*
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE SPECIES FACTORIZATION THEOREM
## Every species of the matching arrangement has the same closed Hilbert series, for every dimension: one product formula, no computation, ever

**Chaise Longue campaign — standalone theorem (referee edition)** · R. Amichis Luengo · Claude (Anthropic) · Auditor: **GETTLER** · 15 August 2026
*Consumes: **Proposition 1.0** (the Odd Symmetric Theorem — `E = (e₁,e₃,…,e_{2k+1})` is radical and a complete intersection, PROVED `∀k`). Engine: `GETTLER_AUDIT_F16_SPECIES_v1.py`, 90+ checks, all PASS.*

---

## 1. Statement

Let `n = 2k+2`. A **species** is a set partition `π` of `[n]` into even blocks. A perfect matching `M` of `[n]` *refines* `π` if every pair of `M` lies inside one block, and
> `X_π = ⋃ { L_M : M refines π }`, `L_M = { x : x_a + x_b = 0 ∀ (a,b) ∈ M }`.

> ### Theorem SF. For every species `π = (2m_1, …, 2m_r)` of `[n]` and every `k`,
> ## `HF_{X_π}(t) = ∏_{j=1}^{r} ∏_{i=1}^{m_j} (1 − t^{2i−1}) ⁄ (1 − t)^{n}`.

*Proof.* Two steps, both one line.
**(a) The arrangement factors.** A matching refines `π = π' ⊔ π''` (a partition of the ground set into two groups of blocks) iff its restriction to each group is a matching refining that group; and `L_{M' ⊔ M''} = L_{M'} × L_{M''}`. Hence `X_π = X_{π'} × X_{π''}` as schemes on complementary variable sets, so the coordinate ring is a tensor product and the Hilbert series is the product.
**(b) Each one-block factor is a complete intersection.** For a single block of size `2m`, `X` is the full matching arrangement on `2m` points, whose vanishing ideal is `E = (e₁, e₃, …, e_{2m−1})` — radical, and a complete intersection of those degrees (Proposition 1.0). Its Hilbert series is `∏_{i=1}^{m}(1−t^{2i−1})/(1−t)^{2m}`. Multiplying over blocks and collecting denominators gives `(1−t)^{Σ 2m_j} = (1−t)^n`. ∎

**Corollary SF.1.** `HF_{X_π}` depends only on the multiset of block sizes, and a size-2 block contributes the factor `(1−t)/(1−t)^2 = 1/(1−t)` — a free line. So appending a size-2 block is exactly cumulative summation.

**Corollary SF.2 (the multiplicities).** The number of species of a given block profile is `mult(π) = n!/(∏_B |B|! · ∏_s c_s!)`, `c_s` = number of blocks of size `s`; in particular the one-block species has multiplicity `1` at every `k`.

---

## 2. Verification

**Independent confirmation, by a completely different method.** An external constructor computed the same table from scratch as GF(3) evaluation ranks — enumerate the matchings refining `π`, restrict every monomial to every sheet by `x_{a_i} = u_i`, `x_{b_i} = −u_i`, take the rank of the resulting matrix — with no knowledge of Proposition 1.0 or of this formula. **All 90+ reported integers agree with Theorem SF exactly**, across `n = 4, 6, 8, 10` and degrees `0 … 9`:

| `n` | species | `HF(0…7)` |
|---|---|---|
| 8 | `2+2+2+2` | 1, 4, 10, 20, 35, 56, 84, 120 |
| 8 | `4+2+2` | 1, 5, 15, 34, 65, 111, 175, 260 |
| 8 | `4+4` | 1, 6, 21, 54, 114, 210, 351, 546 |
| 8 | `6+2` | 1, 6, 21, 55, 120, 230, 400, 645 |
| 8 | `8` | 1, 7, 28, 83, 203, 433, 833, 1477 |
| 10 | `2+2+2+2+2` | 1, 5, 15, 35, 70, 126, 210, 330 |
| 10 | `4+2+2+2` | 1, 6, 21, 55, 120, 231, 406, 666 |
| 10 | `4+4+2` | 1, 7, 28, 82, 196, 406, 757, 1303 |
| 10 | `6+2+2` | 1, 7, 28, 83, 203, 433, 833, **1478** |
| 10 | `6+4` | 1, 8, 36, 118, 314, 719, 1469, 2744 |
| 10 | `8+2` | 1, 8, 36, 119, 322, 755, 1588, 3065 |
| 10 | `10` | 1, 9, 45, 164, 486, 1241, 2829, 5894 |

Degrees 8 and 9 likewise: `495/715`, `1035/1540`, `2107/3241`, `2458/3878`, `4769/7814`, `5516/9366`, and **`11410 / 20775`** for the one-block `n=10` species — of which the last, `HF_{(10)}(9) = 20775`, the machine run did not reach and the formula supplies at no cost.

**Two entries deserve a referee's eye.** The `n=10` species `6+2+2` gives `1, 7, 28, 83, 203, 433, 833, 1478` and the `n=8` one-block species gives `1, 7, 28, 83, 203, 433, 833, 1477`: **seven degrees identical, then a split by exactly one.** They are different rings — a double cumulative sum of the `n=6` series versus the `n=8` complete intersection — and Theorem SF explains both and the split. The same near-coincidence occurs one dimension down (`1,5,15,34,65,111,…` versus `1,5,15,34,65,110,…`, splitting at `d=5`).

---

## 3. What this settles, and what it costs

**Settles.** The graded data of every species, in every dimension, forever. Of any table of `r` species, only the **one-block** rows carry information not forced by the product rule, and those are the complete-intersection series. Two of the three ingredient families the species route needs — the multiplicities and the graded data — are now closed `∀k` in closed form.

**Costs, stated plainly.** The commission that produced the confirming table was **unnecessary, and that was the auditor's error**: the object had a closed form derivable from a theorem the campaign proved a month earlier, and the auditor did not check before commissioning machine time. Registered as the seventh occurrence of `OWN-DEPOSITED-THEOREM-NOT-CONSULTED`, this time against the auditor. **The constructor's work is not wasted — it is an independent confirmation of Proposition 1.0 at four dimensions and ten degrees by a method sharing no step with the algebra — but it is confirmation, not new information, and it is graded that way.**

**Standing rule adopted from it.** *Before commissioning any computation, evaluate every closed form the campaign already owns at the requested cells. If the closed form supplies them, the commission is a confirmation exercise and must be labelled as one before it is sent — never after it returns.*

---

**Grades.** Theorem SF: **PROVED ∀k, ∀π** (two-line proof; 90+ independent numerical confirmations). Corollary SF.2: **PROVED ∀k**. The residue of the species route: the extraction `HF_π ↦ λ_π` (the per-species local head), open, with a three-value gate at `k=3`.

— **GETTLER**, auditor.
