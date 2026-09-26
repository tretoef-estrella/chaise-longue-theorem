> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026 (date not stated in the document)
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE · F-PURITY THRESHOLD THEOREM — v2* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_F_PURITY_THRESHOLD_THEOREM.md
>
> **Status, as written in the document:** Status: PROVED ∀k. A clean degree threshold for the F-purity of the odd-elementary complete intersection, and the corollary that levelness at `k≥2` is NOT an F-purity consequence (it survives F-impurity).
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (2 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v2`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE · F-PURITY THRESHOLD THEOREM — v2
### Constructor: Lacassagne · Auditor: Gross (audited line-by-line + gated `k=1..6`, `GF(3)`) · char 3
### Status: **PROVED ∀k.** A clean degree threshold for the F-purity of the odd-elementary complete intersection, and the corollary that **levelness at `k≥2` is NOT an F-purity consequence** (it survives F-impurity).

---

## Statement
Let `S = F_3[x_0,…,x_{2k+1}]` (`n = 2k+2` variables, char `p = 3`), and let `E = (e_1, e_3, …, e_{2k+1})` be the odd elementary symmetric polynomials (a complete intersection, `ODD_ELEMENTARY_CI`). Then:

> ## **THEOREM (F-purity threshold, all Frobenius levels). `S/E` is `F^e`-pure ⟺ `k ≤ 1`, for EVERY `e ≥ 1`.**
> In particular no higher Frobenius power rescues `k≥2`: `F, F², F³,…` all fail identically.

**Corollary (the genuine subtlety).** Levelness of `A = S/(E + m^{[q]})` holds (measured `k=1,2`) at values of `k` where `S/E` is F-IMPURE (`k ≥ 2`). Hence **levelness at `k≥2` is not explained by, and does not follow from, F-purity of `S/E`.** The socle-concentration `soc(A)⊆A_T` is a finer phenomenon that survives an impure Frobenius.

---

## Proof (Fedder's criterion + a degree count)
**Fedder's criterion (level `e`).** `S/E` is `F^e`-pure ⟺ `(∏_i g_i)^{p^e−1} ∉ m^{[p^e]}`. The degree count: `deg(∏e_i)^{p^e−1} = (p^e−1)(k+1)²`, escape degree `= (p^e−1)·2n = (p^e−1)·2(k+1)·2`… more precisely a monomial escapes `m^{[p^e]}` iff all exponents `≤ p^e−1`, max degree `(p^e−1)(2k+2)`. So `F^e`-pure ⟺ `(p^e−1)(k+1)² ≤ (p^e−1)(2k+2)` ⟺ `(k+1)² ≤ 2(k+1)` ⟺ `k≤1` — **`(p^e−1)` cancels, so the threshold is independent of `e`.** Gated `e=1,2,3`, `k=1,2,3` (`k=1` boundary `8=8, 32=32, 104=104`; `k≥2` strictly impure). The `e=1` case is: `(∏_i g_i)^{p−1} ∉ m^{[p]}`, where `m^{[p]} = (x_0^p,…,x_{2k+1}^p)`.

**The product degree.** `∏_i e_i = e_1 e_3 ⋯ e_{2k+1}`, so
`deg ∏_i e_i = Σ_{i=1}^{k+1} (2i−1) = (k+1)²`, hence `deg (∏_i e_i)^{p−1} = (p−1)(k+1)² = 2(k+1)²`.

**The escape degree.** A monomial lies OUTSIDE `m^{[3]}` iff every exponent is `≤ 2`. The maximum degree of such a monomial in `n = 2k+2` variables is `2n = 4(k+1)`. Therefore `(∏_i e_i)^{p−1}` can have a monomial escaping `m^{[3]}` only if
`2(k+1)² ≤ 4(k+1) ⟺ (k+1) ≤ 2 ⟺ k ≤ 1.`

**The two directions.**
- `k ≥ 2`: `2(k+1)² > 4(k+1)`, so EVERY monomial of `(∏e_i)^{p−1}` has degree `> 4(k+1)`, hence (pigeonhole over `2k+2` variables) at least one exponent `≥ 3`, i.e. lies in `m^{[3]}`. So `(∏e_i)^{p−1} ∈ m^{[3]}` — **F-IMPURE.**
- `k = 1`: `2(k+1)² = 8 = 4(k+1)`; the degree-8 monomial with every exponent exactly `2` survives with nonzero coefficient (gated: exactly one escaping monomial), so `(∏e_i)^{2} ∉ m^{[3]}` — **F-PURE.**
- `k = 0`: trivially F-pure. ∎

---

## Gate (Gross, `GF(3)`, byte-exact)
`deg (∏e_i)^{p−1} = 2(k+1)²` vs escape degree `4(k+1)`:
- `k=1`: `8 = 8`, **1** escaping monomial → F-pure ✓
- `k=2`: `18 > 12`, **0** escaping → F-impure ✓
- `k=3..6` (`e=1`): `32>16, 50>20, 72>24, 98>28`, **0** escaping → F-impure ✓
- all `e`: `(p^e−1)` cancels ⟹ same `k≤1` threshold (gated `e=1,2,3`) → **no higher Frobenius rescues `k≥2`** ✓
Engine `gate_fpure.py`. No number invented; `p=3` used correctly (Fedder), never `Q`.

## Consequences for GAP 3 (honest, negative = information)
This BURIES the "clean Frobenius quench" reading of levelness: the split fails for `k≥2`, yet the blade is true. Combined with the earlier catches, the levelness phenomenon at `k≥2` is now known NOT to come from any of: `δ₀`/doubled-ring reducedness, the `q→3q` tower, the GAP-B one-dimension leak, or F-purity of `S/E`. The remaining legitimate, on-object frame is **F-INJECTIVITY (strictly weaker than F-pure) / the a-invariant of `S/E`**, or the canonical module `ω_A = ann_Λ(J)` generated in degree `T` over the Gorenstein ceiling `Λ` (`F̄_3`). `G` stays 3.

---
*Cite as `F_PURITY_THRESHOLD_THEOREM_v1`. Depends on: `ODD_ELEMENTARY_CI_THEOREM_v1` (E a CI), Fedder's criterion. Companion negative to the levelness thread. — Gross & Lacassagne*
