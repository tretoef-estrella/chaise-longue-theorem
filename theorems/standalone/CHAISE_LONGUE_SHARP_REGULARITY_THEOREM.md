> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-23
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE SHARP REGULARITY LAW — CHAISE_LONGUE_SHARP_REGULARITY_THEOREM_v1* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_SHARP_REGULARITY_THEOREM.md
>
> **Status, as written in the document:** Summary. `C.4` has been carried by this campaign as *"CANDIDATE 6/6"* and described in the sovereign
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (2 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE SHARP REGULARITY LAW — `CHAISE_LONGUE_SHARP_REGULARITY_THEOREM_v1`
### `C.4` for the letter `B_m`: `deg N_G = C(m,2) = reg`, for every `m`, as a corollary of two theorems already deposited
**Chaise Longue campaign · 23 Jul 2026 · Orfila (auditor)**

> **Summary.** `C.4` has been carried by this campaign as *"CANDIDATE 6/6"* and described in the sovereign
> document as **"a nail to be fabricated"**. It is not a nail. It is a **five-line corollary** of two
> results that were already in the catalogue, proved for all `m`, and never multiplied together:
> `T1` (the letter Hilbert series) and the **Letter Census Theorem** for `B_m`. The whole
> `C`-Cohen–Macaulay campaign was a route to a *sufficient* condition for `C.4`. The target itself was
> reachable without it.

---

## 1. THE TWO INPUTS, BOTH ALREADY DEPOSITED

**(I) `T1` — the letter Hilbert series *(PROVED ∀m, `STANDALONE_T1_LETTER_HILBERT`)*:**

>  `H(B_m) = [m]_t! / (1−t)^m`,  where `[i]_t = 1 + t + … + t^{i−1}` and `[m]_t! = ∏_{i=1}^m [i]_t`.

**(II) The Letter Census Theorem *(PROVED ∀m with its declared residue, `LETTER_CENSUS_THEOREM_Bm_v2`)*,
in the equivalent form used by the campaign since `A24`:**

>  `Hilb(C) = h_m(t) / (1−t)^{m−1}`,  with `C = m·H − G` the defect module,
>  and **Teorema A** *(PROVED ∀m, `CORE_FACTORIZATION_THEOREM_v1`)*: `h_m = [m−2]_t! · q_m`,
>  `q_m = [m−1]_t [m]_t (Σ_{i<m} [i]_t) − t^{m−1} S_m²`,  `S_m = Σ_{i=1}^{m−1} i t^{m−1−i}`.

Nothing else is used. In particular **no Cohen–Macaulayness of anything is used.**

---

## 2. THE COMPUTATION

From `C = m·H − G` and the two Hilbert series,

>  `G = m·[m]_t!/(1−t)^m − h_m/(1−t)^{m−1} = [ m·[m]_t! − (1−t)·h_m ] / (1−t)^m`,

so, in the campaign's normalisation (denominator `(1−t)^m`),

> ### `N_G = m·[m]_t! − (1−t)·h_m`.

---

## 3. THEOREM *(PROVED, all `m ≥ 1`)*

> ### `deg N_G = C(m,2) = reg`, and the leading coefficient is `2m − 1`.

**Proof, five lines.**

1. `deg [m]_t! = Σ_{i=1}^m (i−1) = C(m,2)`, with leading coefficient `1`.
2. By Teorema A, `deg h_m = deg[m−2]_t! + deg q_m = C(m−2,2) + 2(m−2)`. And
   `C(m−2,2) + 2(m−2) = [(m−2)(m−3) + 4(m−2)]/2 = (m−2)(m+1)/2 = (m² − m − 2)/2 = C(m,2) − 1`.
3. `h_m(0) = q_m(0) = m−1` (at `t = 0`: `[m−1]_0 = [m]_0 = 1`, `Σ_{i<m}[i]_0 = m−1`, and
   `t^{m−1}S_m²` vanishes for `m ≥ 2`). Since `[m−2]_t!` and `q_m` are palindromic, so is `h_m`, hence
   its **leading** coefficient also equals `m−1`.
4. Therefore `deg (1−t)h_m = C(m,2)`, with leading coefficient `−(m−1)`.
5. The coefficient of `t^{C(m,2)}` in `N_G = m·[m]_t! − (1−t)h_m` is `m·1 − (−(m−1)) = **2m − 1**`,
   which is non-zero for every `m ≥ 1`. Nothing above it survives, since both terms have degree
   `C(m,2)`. ∎

**Constant term.** `N_G(0) = m·1 − h_m(0) = m − (m−1) = 1`, for every `m`.

---

## 4. GATES — EVERY SEALED NUMBER IN THE ARCHIVE, REPRODUCED

Declared before reading anything, and all passed:

```
  N_G(B_4)  computed  1, 4, 9, 24, 31, 20, 7      archive  1, 4, 9, 24, 31, 20, 7     byte-exact
  N_G(B_5)  leader 9  (archive: 9)   constant 1  (archive: 1)   sum 600 = m*m!  (archive: 600)
  N_G(B_3)  computed  1, 3, 9, 5                  degree 3 = C(3,2)

  G(B_2) = 1,5,9,13                       sealed  1,5,9,13                 OK
  G(B_3) = 1,6,24,60,114,186,276          sealed  same                     OK
  G(B_4) = 1,8,35,120,332,760             sealed  same                     OK
  G(B_5) = 1,10,54,209,665                sealed  same                     OK
  h_3 = 2,5,2      h_4 = 3,11,22,22,11,3  sealed  same                     OK
  H(B_3) = 1,5,14,29,50,77,110  H(B_4) = 1,7,27,76,174,344  H(B_5) = 1,9,44,155,440   OK

  deg N_G  vs  C(m,2)   and  leader vs 2m-1,  m = 2..8
     m=2: 1 vs 1, 3 vs 3     m=3: 3 vs 3, 5 vs 5      m=4: 6 vs 6, 7 vs 7
     m=5: 10 vs 10, 9 vs 9   m=6: 15 vs 15, 11 vs 11  m=7: 21 vs 21, 13 vs 13
     m=8: 28 vs 28, 15 vs 15
```

The reproduction of `N_G(B_4) = 1,4,9,24,31,20,7` coefficient by coefficient is the decisive check: that
vector was measured by an engine, independently of any closed form, and it is recovered here from `T1`
and Teorema A alone.

---

## 5. WHAT THIS DOES TO THE CRITICAL PATH

The Golden Reduction (`G1`/`G2`/`G3`, TANDA2) reads: **`C` Cohen–Macaulay ⟹ `deg N_G = reg` exactly.**
That is a *sufficient* condition. `C.4` is the conclusion, not the hypothesis.

> **`C.4` is now proved directly. Cohen–Macaulayness of `C` is no longer on the critical path for it.**

The `C`-CM campaign produced real theorems — `W` fixed for all `m`, the swap duality law, the equivariant
Betti table of `C(B_3)`, `C` absolutely indecomposable, `C`-CM ⟺ `Γ` MCM — and none of them is retracted.
But **they were a route to a sufficient condition for a statement that follows in five lines from the
catalogue.** That is worth saying plainly rather than dressing up.

---

## 6. SCOPE — WHAT IS **NOT** CLAIMED

1. **This is the `B_m` half of `C.4` only.** The other half, `deg N_G(Z_m) = m(m−1)`, is **not** proved
   here: it needs the analogue of Teorema A for the `Z` letter, which does not exist on file.
2. **It inherits the declared residue of `LETTER_CENSUS_THEOREM_Bm_v2`** — the shift/flat-to-flat
   connection is verified in aggregate, not from first principles. Whatever that residue costs, this
   corollary costs the same. It is not independent evidence for the letter theorem.
3. **It does not, by itself, close `GAP 1`.** The sovereign document's own reduction says
   `C.4 ⟹ GAP 1 + PASO 0-sharp`, but that chain has **not** been audited line by line against the
   assembly draft in this deposit, and the sovereign document has stated the reduction in two
   non-equivalent ways across versions (`v72` routes `GAP 1` through the symbolic assembly; `v74` routes
   it through `C.4`). **Auditing that chain is the next action, and it is exactly the `PASO X3` debt that
   has been open for weeks.**
4. Nothing here proves `C` Cohen–Macaulay, and nothing here retracts any measurement.

**Reproduction:** `c4_check.py` (Python 3 + sympy), which recomputes `N_G` from `T1` and Teorema A for
`m = 2..8` and gates it against every sealed series in the archive.

— Orfila, Chaise Longue campaign
