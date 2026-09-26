> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-23
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE CORE FACTORIZATION THEOREM FOR THE DEFECT MODULE* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_CORE_FACTORIZATION_THEOREM.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE CORE FACTORIZATION THEOREM FOR THE DEFECT MODULE
## Chaise Longue campaign — standalone deposit v1
**Author:** Lacassagne (constructor) · **Audit:** Orfila · **Architect:** Rafa · 23 Jul 2026

---

## ABSTRACT

Let `B_m` denote the bipartite letter of the Chaise Longue campaign: `R = F_3[a_1..a_m, b_1..b_m]`,
`I_B = (e_j(a) - (-1)^j e_j(b))_{j=1..m}` a complete intersection of degrees `1,...,m`, and
`H = Hilb(R/I_B)`. Let `G = N_G` be the census module and `C = m·H − G` the **defect module**,
whose Hilbert series is `Hilb(C) = h_m(t)/(1−t)^{m−1}` with `h_m` the (proven) h-vector polynomial.

We prove that `h_m(t)` **factors**, for every `m ≥ 3`, as

>   **`h_m(t) = [m−2]_t! · q_m(t)`,  where  `q_m(t) = [m−1]_t [m]_t (Σ_{i=0}^{m−1} [i]_t) − t^{m−1} S_m(t)^2`**

with `[j]_t = 1 + t + ... + t^{j−1}`, `[j]_t! = ∏_{d=1}^{j}[d]_t`, and `S_m(t) = Σ_{i=1}^{m−1} i·t^{m−1−i}`.

The proof is two lines of elementary Gauss-binomial algebra (Lemma 1). Its consequences are
structural: the numerator `[m−2]_t!` is exactly the Koszul factor of a regular sequence of degrees
`1,...,m−2`, and the residual `q_m` is the h-vector numerator of a hypothetical **core module `D`**
of dimension `2m−3`, hence of **codimension 3 independently of `m`**, and of degree
`q_m(1) = C(m,2)^2`. We further record the graded Betti table forced on the core by these data,
verified byte-exact against two fully computed minimal free resolutions (`m=3, 4`), and the exact
identification of the core's support as a union of `C(m,2)^2` codimension-3 linear subspaces.

**What this theorem does NOT claim is stated explicitly in §5 and is essential to its correct use.**

---

## 1. NOTATION AND STANDING FACTS (imported, not proved here)

- **(F1)** `Hilb(R/I_B) = H = [m]_t! / (1−t)^m`. *(complete intersection of degrees 1..m)*
- **(F2)** `G = N_G = H·[m]_t + t^{m−1}·[m−2]_t!·S_m(t)^2 / (1−t)^{m−1}` (free part + flat torsion).
- **(F3)** `C = m·H − G`, `dim C = m−1`, so `Hilb(C) = h_m(t)/(1−t)^{m−1}` with `h_m` a polynomial.
- **(F4)** `deg C = h_m(1) = C(m,2)^2 · (m−2)!` = number of swap flats of `B_m`.
- **(F5)** `reg = C(m,2)` (Golden Reduction, TANDA2).

Facts (F1)–(F5) are imported from the campaign's sealed corpus and are **not** re-derived here.

---

## 2. THE FACTORIZATION

**LEMMA 1 (Gauss-binomial identity).** For every `m ≥ 1`,
`m − [m]_t = (1−t) · Σ_{i=0}^{m−1} [i]_t`.

*Proof.* `m − [m]_t = Σ_{i=0}^{m−1} (1 − t^i)` and `1 − t^i = (1−t)[i]_t`. ∎

**LEMMA 2 (splitting the factorial).** `[m]_t! = [m−2]_t! · [m−1]_t · [m]_t` for `m ≥ 2`. ∎

**THEOREM A (Core Factorization).** For every `m ≥ 3`,
`h_m(t) = [m−2]_t! · q_m(t)` with `q_m` as in the Abstract; in particular `[m−2]_t!` divides `h_m`
in `Z[t]`.

*Proof.* From (F1)–(F3),
`C = [m]_t!(m − [m]_t)/(1−t)^m − t^{m−1}[m−2]_t! S_m^2/(1−t)^{m−1}`.
Multiplying by `(1−t)^{m−1}` gives `h_m = [m]_t!(m−[m]_t)/(1−t) − t^{m−1}[m−2]_t! S_m^2`.
By Lemma 1 the first term equals `[m]_t! · Σ_{i<m}[i]_t`; by Lemma 2 this is
`[m−2]_t! · [m−1]_t [m]_t Σ_{i<m}[i]_t`. Both terms carry the factor `[m−2]_t!`. ∎

**COROLLARY A1.** `q_m` is palindromic for every `m`; `deg_t q_m = 2(m−2)`;
`q_m(1) = C(m,2)^2 = reg^2` by (F5).

**COROLLARY A2 (dimension collapse).** If a graded `R`-module `D` satisfies
`Hilb(D) = q_m(t)/(1−t)^{2m−3}` and `C = D/(f_1,...,f_{m−2})D` for a `D`-regular sequence of degrees
`1,...,m−2`, then `dim D = 2m−3` and **`codim D = 2m − (2m−3) = 3` for every `m`**.

*Verification:* Theorem A verified symbolically for `m = 3,...,9`; Corollaries for `m = 3,...,12`.

---

## 3. THE GRADED BETTI TABLE FORCED ON THE CORE

Write `β'_{i,j}` for the graded Betti numbers of the conjectural core `D`, `c' = 3`, shift `s' = 2m−1`.

**PROPOSITION B.** The table
```
β'_{0,0}       = m−1
β'_{1,j}       = 1              for j = 1, ..., m−2
β'_{1,m−1}     = m² − m + 1
β'_{2,m}       = m² − m + 1
β'_{2,j}       = 1              for j = m+1, ..., 2m−2
β'_{3,2m−1}    = m−1
```
(a) reproduces **exactly** the cores extracted from the two fully computed minimal free resolutions,
`m=3 → (2,8,8,2)` and `m=4 → (3,15,15,3)`;
(b) is self-dual, `β'_{i,j} = β'_{3−i, (2m−1)−j}`;
(c) has column totals `(m−1)·(1, m+1, m+1, 1)`;
(d) satisfies the Euler identity `Σ_{i,j} (−1)^i β'_{i,j} t^j = q_m(t)·(1−t)^3`, in the closed form
`(m−1)(1−t^{2m−1}) − t[m−2]_t(1−t^m) − (m²−m+1)t^{m−1}(1−t)`.

*Verification:* (a) byte-exact at `m=3,4`; (b)(c)(d) symbolically for `m = 3,...,12`.

**Status of Proposition B: MEASURED at m=3,4 and CONSISTENT ∀m in the tested range.**
It is a necessary condition on any resolution of `D`, **not** a proof that such a resolution exists.

---

## 4. THE SUPPORT OF THE CORE

For a pair of transpositions `τ_a = (i j)` on the `a`-side and `τ_b = (k l)` on the `b`-side, set
`V_{τ_a,τ_b} = V( a_i − a_j , b_k − b_l , a_i + b_k ) ⊂ A^{2m}`, a linear space of codimension 3.

**PROPOSITION C.** `U' = ∪_{τ_a,τ_b} V_{τ_a,τ_b}` consists of `C(m,2)^2` such spaces, and at `m=3`
satisfies `dim U' = 3 = 2m−3` and `deg U' = 9 = C(m,2)^2`, both byte-exact against Corollary A2.
Moreover the fibre count `#{swap flats} = C(m,2)^2 · (m−2)!` of (F4) is explained: a swap flat
`L_π ∩ L_{π∘(ij)}` equals `L_π ∩ {a_i = a_j}` and determines the pair `((i j), (π(i) π(j)))`;
the remaining `m−2` indices may be matched in `(m−2)!` ways.

**PROPOSITION D (three candidates eliminated with data, at `m=3`).**
| candidate | HF deg 0..3 | Betti | verdict |
|---|---|---|---|
| target `D` (from `q_3`) | `2, 11, 29, 56` | `(2,8,8,2)` | — |
| `O(U')` | `1, 6, 21, 45` | `(1,11,18,9,1)`, `pd = 4` | **≠ D**, and not CM |
| `ω_{O(U')} = Ext³(O(U'),R)` | `4, 16, 37, 67` | `(4,8,6,2)`, `pd = 3` | **≠ D**, but *is* CM |

The third row is informative in the positive direction: **CM rank-one modules supported on `U'` exist.**

---

## 5. SCOPE — WHAT THIS THEOREM DOES *NOT* CLAIM

1. **It does not prove that `C` is Cohen–Macaulay**, for any `m`. CM is measured at `m=3, 4` only.
2. **It does not prove that the core module `D` exists.** Theorem A is an identity between Hilbert
   series numerators. The existence of `D` with `Hilb(D) = q_m/(1−t)^{2m−3}`, and of a `D`-regular
   sequence `f_1,...,f_{m−2}` with `C = D/(f_1,...,f_{m−2})D`, is **conjecture**.
3. **It does not prove that the minimal free resolution of `C` is a tensor product**
   `Koszul(f_1,...,f_{m−2}) ⊗ G_•`. The observed factorisation is of *Betti polynomials* at `m=3,4`;
   a factorisation of polynomials is evidence for, not proof of, a tensor decomposition of complexes.
4. **It does not construct `G_•`,** and it does not prove exactness of any complex. Closing the
   Cohen–Macaulayness of `C` for all `m` requires an explicit `G_•` **plus** an exactness proof
   (the appropriate instrument being the Buchsbaum–Eisenbud acyclicity criterion: rank conditions
   together with depth bounds on the ideals of minors). Neither is supplied here.
5. **It does not identify `D`.** Proposition D eliminates the two most natural candidates.
6. Proposition B is verified in a finite range (`m ≤ 12`) and Proposition C at `m=3` only.
   Theorem A and its corollaries are the only statements herein proved for all `m`.

---

## 6. PROVENANCE

- `h_m` closed form, (F1)–(F4): campaign corpus, sealed; reproduced independently by Lacassagne
  (`[2,5,2]`, `[3,11,22,22,11,3]`, masses `9 / 72 / 600`).
- `pd(C(B_3)) = 4 = codim`, `pd(C(B_4)) = 5 = codim`: computed by Orfila in Macaulay2 over `F_3`,
  gated on Hilbert numerator, `dim`, and `degree` before the verdict was read.
- Graded Betti tables `m=3,4`: Orfila; **independently verified by Lacassagne** against the sealed
  Hilbert series via the K-polynomial identity `K(t) = h_m(t)(1−t)^{m+1}`, which both satisfy exactly.
  The `m=4` table as first printed was **not minimal** (`β_0 = 4` against `HF(C)(0) = h_0 = 3`, with a
  spurious degree-0 syzygy); the minimal table `3, 21, 48, 48, 21, 3` is the one used here.
- Theorem A, Propositions B, C, D: Lacassagne, this deposit.
- Route history: reached after the free-resolution route was shown **not** to bypass the mid-degree
  obstruction that had already stopped the depth telescope (TANDA6) and self-duality (MIRROR).
  The dead ends `C ≠ O(U)`, `C ≠ ω_U`, `C ≠ χ(flat nerve)`, `C ≠ χ(sheet nerve)` and the rank-one
  reading `deg C = #swap flats` (against the `O(F)^{m−1}` label of L1, buried as
  `SPLIT-RANK-M1-IS-NOT-C`) are what forced the search into the factorised form proved above.

---

**Grade of every statement in this document is stated inline. Nothing here is asserted bare.**
**The magic word is not spoken: PASO 1 remains open.**
