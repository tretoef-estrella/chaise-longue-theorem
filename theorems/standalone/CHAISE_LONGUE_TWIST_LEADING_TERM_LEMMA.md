> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026 (date not stated in the document)
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE_LONGUE_TWIST_LEADING_TERM_LEMMA_v1* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_TWIST_LEADING_TERM_LEMMA.md
>
> **Status, as written in the document:** Grade: PROVED ∀k (the generator-leading-term half of STEP 1b). Char ≠ 2; stated over `F_3`. Gated `(1,3),(1,5),(2,3)`.
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE_LONGUE_TWIST_LEADING_TERM_LEMMA_v1
### Standalone lemma · Constructor: Lacassagne · campaign Chaise Longue · GAP 3 (Matlis-dual descent, STEP 1b)
### Grade: **PROVED ∀k** (the generator-leading-term half of STEP 1b). Char ≠ 2; stated over `F_3`. Gated `(1,3),(1,5),(2,3)`.
### ⚠️ PARTIAL: this does NOT close STEP 1b — see Scope. It proves the two leading-term facts the mission asked for, and pinpoints why they are not sufficient.

---

## Setup

`B'' = F_3[w_0,…,w_{2k−1}]`, grevlex with `w_0 > w_1 > … > w_{2k−1} = z` (so `z` is the **smallest**
variable). `e_m` = elementary symmetric of degree `m` in all `2k` variables. The `(1−zτ)²`-twisted odd
generators (from `DUAL_PAIR_COLLAPSE_LEMMA_v1`):
`Ê_j = e_j + z·e_{j−1} + z²·e_{j−2}`, `j = 1,3,…,2k+1`.
`E_{k−1} = (e_1,e_3,…,e_{2k−1})` is the plain level-`(k−1)` odd-symmetric ideal.

> **LEMMA.**
> **(i)** For `j = 1,3,…,2k−1`: `lm(Ê_j) = lm(e_j) = w_0 w_1 ⋯ w_{j−1}`.
> **(ii)** For `j = 2k+1`: `Ê_{2k+1} = z·e_{2k} + z²·e_{2k−1}` and
> `lm(Ê_{2k+1}) = −w_0 w_1 ⋯ w_{2k−2}·z² = lm(e_{2k−1})·z²`, a **multiple of** `lm(e_{2k−1})`.

---

## Proof (∀k)

**(i)** Fix odd `j ≤ 2k−1`. All monomials of `Ê_j` have total degree `j`. In grevlex, among degree-`j`
monomials the one with the **smaller** exponent of the smallest variable `z` is the **larger**.
`lm(e_j) = w_0 w_1 ⋯ w_{j−1}` (the `j` largest variables; since `j ≤ 2k−1 < 2k` it excludes `z`) has
`z`-exponent `0`, so it is grevlex-larger than every degree-`j` monomial with `z`-exponent `≥ 1`. Every
monomial of `z·e_{j−1}` and of `z²·e_{j−2}` has `z`-exponent `≥ 1`. Hence `lm(Ê_j) = lm(e_j)`.

**(ii)** With only `2k` variables, `e_{2k+1} = 0`, so `Ê_{2k+1} = z·e_{2k} + z²·e_{2k−1}`. Now
`e_{2k} = w_0 ⋯ w_{2k−1} = (w_0 ⋯ w_{2k−2})·z`, so `z·e_{2k} = (w_0 ⋯ w_{2k−2})·z²`. In `z²·e_{2k−1}`
the single term that omits `z` is `z²·(w_0 ⋯ w_{2k−2})`; every other term of `e_{2k−1}` contains `z`,
giving `z`-exponent `≥ 3`. The two `z²`-exponent contributions add: coefficient `1 + 1 = 2 = −1` on
`w_0 ⋯ w_{2k−2}·z²`, which is grevlex-maximal (`z`-exponent `2`, all remaining terms have `z`-exponent
`≥ 3`). Hence `lm(Ê_{2k+1}) = w_0 ⋯ w_{2k−2}·z² = lm(e_{2k−1})·z²`. ∎

---

## Scope — what this proves, and the exact gap it leaves

- **Proves ∀k:** the *given-generator* leading terms of `Ê` coincide with those of `E_{k−1}` for
  `j ≤ 2k−1`, and the extra top generator `Ê_{2k+1}` is **initial-redundant** relative to `E_{k−1}`'s
  generators (its leading term is a multiple of `lm(e_{2k−1})`). (These are exactly death-criteria 1–2
  of `MISSION_STEP1B_STEP2` — **both PASS ∀k**.)
- **Does NOT prove** `in(Ê + m^{[q]}) = in(E_{k−1} + m^{[q]})`. Matching generator leading terms does
  **not** imply matching initial ideals: both ideals need Gröbner completion, and the completion is
  strictly larger than the generator leading terms. **Measured at `k=2→1, q=3`:**
  `in(E_{k−1}+m^{[q]}) = (w_0, w_1²w_2, w_1 w_2² z, w_1³, w_2³, z³)` — the terms `w_1²w_2` and `w_1 w_2² z`
  are **completion** leading terms, not multiples of any generator leading term. So `{e_1,e_3}∪box` is
  **not** a Gröbner basis, and the mission's inference "generator LTs match ⟹ initial ideals equal" is
  **incomplete**.
- The completion leading terms *do* coincide for `Ê` and `E_{k−1}` at `(1,3),(1,5),(2,3)` (so
  `dim(B''/Ê·B'') = A_{k−1}(q) = 3,5,19` there), but the completion-matching is **open ∀k**. **STEP 1b is
  NOT closed;** `G` stays 3.

**Engine:** `step1b_initial_ideal_lacassagne.py` (Gröbner over `GF(3)`, grevlex).
**Depends on:** `DUAL_PAIR_COLLAPSE_LEMMA_v1` (defines `Ê`, the `(1−zτ)²` twist).
**Feeds:** STEP 1b of `MISSION_STEP1B_STEP2` (the residual is exactly the completion-matching).

— Lacassagne
