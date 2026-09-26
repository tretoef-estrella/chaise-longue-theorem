> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-14
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE CASCADE COLLAPSE THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_STANDALONE_CASCADE_COLLAPSE.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (5 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v0`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE CASCADE COLLAPSE THEOREM
## The crude collar ceiling as the graded structure of one Koszul complex: `z_k(q,f) = Σ_{j≥2}(−1)^j C(k+1,j)·C(f−(j−2)q+k, k)` for every dimension, every tower level, every degree — the former "cascade guillotine", now exact

**Chaise Longue campaign — standalone theorem write-up (referee edition)** · R. Amichis Luengo · Claude (Anthropic) · 14 July 2026
*Source: CHAISE_LONGUE_CASCADE_COLLAPSE_THEOREM_v1, audited (the theorem that removed the last structural conditional of the Silver Bridge, per Concentrado §3.9). This document is used in two papers: it is the crude-ceiling half of the Hammock's sharpened collar (dimension six), and it is the all-`k` structural theorem that makes the collar ceiling a closed form for every dimension. Both roles are stated in §5.*

---

### 1. The object and the former obstacle

On each sheet `V_J` of the arrangement, the collar analysis produces a system in the `k+1` power elements `(u₁^q, …, u_{k+1}^q)` (the pair coordinates raised to the Frobenius power). The **crude ceiling** `z_k(q,f)` counts the syzygy room at cofactor degree `q + f` before any sharpening. The campaign's original plan feared a "cascade": at higher collar levels (`f ≥ q`, `f ≥ 2q`, …) multiple heavy slots open, and a naive analysis would require an unbounded ladder of level-by-level constructions — the "guillotine" that threatened an all-`k` proof.

### 2. Theorem (Cascade Collapse)

> **Theorem.** On each sheet the sequence `(u₁^q, …, u_{k+1}^q)` is a **regular sequence** (the `u_i` are the `k+1` independent linear coordinates of the `(k+1)`-dimensional sheet, and Frobenius powers of a regular sequence of linear forms are regular). Therefore the **Koszul complex** `K_•(u₁^q,…,u_{k+1}^q)` is exact, and the crude ceiling is its graded Euler characteristic in the relevant degree:
> **`z_k(q, f) = Σ_{j≥2} (−1)^j C(k+1, j)·C(f − (j−2)q + k, k)`**
> for every `k`, every `q`, every `f` (binomials with top `< k` read as zero).
*Proof.* Exactness of the Koszul complex on a regular sequence is standard; the graded pieces of `K_•` are `⊕ S(−j·q)` shifted copies (choosing `j` of the `k+1` powers), whose degree-`(q+f)` dimensions are the binomials `C(k+1,j)·C(f−(j−2)q+k, k)` after accounting for the two ambient powers already spent (the `(j−2)` shift). The alternating sum over `j ≥ 2` is the ceiling (the `j = 0, 1` terms are the ambient and single-power pieces removed by the transfer identity). Every "level" `r ≥ 2` of the old cascade is now simply the range of `f` where the `j = r+1` term becomes nonzero — ONE complex, read through a moving degree window, not a ladder of constructions. ∎

### 3. Consequence: the last conditional removed
Because the ceiling is now a single closed form valid for all `f` (all levels at once), the **Silver Bridge becomes unconditional for every `k`**: there is no remaining "level `r ≥ 2` construction" to prove — the Koszul exactness supplies them all simultaneously. The campaign's structural skeleton has, after this theorem, **zero structural conditionals**; everything remaining is finite toll (the sharp-ceiling identity, i.e. the slack).

### 4. Verification record
- **Dimension six, `q = 9`:** `z_3(9, f)` reproduces the crude collar ceiling **9/9** against the real census slicing, **including level 2** (`f ≥ q`, where the `j = 3` term switches on) — the decisive check, since level 2 is exactly what the old "cascade" feared.
- **Consistency:** the alternating structure vanishes below `f = 0` and matches the transfer identity's coarse terms where they overlap.

### 5. The two roles (which paper consumes this)
**(a) Hammock (dimension six):** `z_3(q, f)` is the crude ceiling that, minus the Unified Slack Law of dimension six (companion standalone), gives the sharpened collar ceilings clamping to `B₃(q)`.
**(b) Chaise Longue (all `k`):** the theorem is the all-`k` structural result that makes the crude collar ceiling a closed form in every dimension — the object the all-`k` sharp-ceiling program (per-band Golpe-2 parametrized) must sharpen, with its budget written (Collar Budget standalone).

### 6. Attack surface
(A) The regular-sequence claim (Frobenius powers of linearly independent linear forms — verify independence on each sheet; the `u_i` ARE a coordinate system of `V_J`, so it is immediate, but state it). (B) The graded bookkeeping of the shift `(j−2)q` (which two powers are "already spent" — the transfer identity's role; re-derive the exponent). (C) The `q = 9` level-2 check (rerun the slicing; this is the check that retired the guillotine). (D) The binomial vanishing convention (top `< k ⟹ 0`) at the band edges. (E) External: any error would break the 9/9, which includes the one level that a naive theory gets wrong.

**Anchors.** CHAISE_LONGUE_CASCADE_COLLAPSE_THEOREM_v1 · Concentrado v5 §3.9 (the conditional-removal role) · Silver Bridge standalone (the theorem it unconditionalizes) · Unified Slack Law and Collar Budget standalones (the two consumers) · q = 9 census log (9/9). github.com/tretoef-estrella.
