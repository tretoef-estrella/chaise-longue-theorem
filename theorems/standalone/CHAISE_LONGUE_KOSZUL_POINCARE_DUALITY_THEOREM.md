> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-25
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE KOSZUL–POINCARÉ DUALITY THEOREM (v2)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_KOSZUL_POINCARE_DUALITY_THEOREM.md
>
> **Status, as written in the document:** Remark (why v1 was weaker). v1 used only `\mathrm{grade}(x^{[q]},R) = k+1` and got `i=0`. The finite-length observation (I1) is what upgrades one case to all of them, because it makes the dualizing functor exact on the whole homology.
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (2 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v2`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE KOSZUL–POINCARÉ DUALITY THEOREM (v2)
### The full duality `H_{k+1-i} ≅ H_i^\vee(-a-nq)` for every `i`, not just the top — with the Euler identity, and the generators↔socle dictionary it produces
### Constructor: **Bisel** · 25 August 2026 · Pending P0 · char `K ≠ 2`, `q` odd
### **v2 supersedes v1**, which proved only the case `i = 0`. The mechanism that gives all `i` is stated in §3.1 and is the new content.

**Certificado Ley 41.** Object: the graded Koszul homology `H_•(x^{[q]};R)` over the odd-elementary CI and its duality. `DEFECT_TOR_LOCALIZATION_THEOREM_v1` records `\operatorname{Tor}_i(M,B) = H_i(x^{[q]};M)` and computes the defect as a `\mathrm{coker}`; it states **no** duality, identifies **no** `H_i`, and never uses that `R` is Gorenstein. `CASCADE_COLLAPSE` is per-sheet over `O(V_J)`, a different ring. No tomb shares the object. **Pillars:** (i) Odd Symmetric; (ii) Point-Count.

---

## 1. Setting
`\mathrm{char}\,K ≠ 2`, `q` odd, `n = 2k+2`, `S = K[x_0,…,x_{n−1}]`, `E = (e_1,e_3,…,e_{2k+1})`, `R = S/E`, `A = R/(x^{[q]})R = S/(E+m^{[q]})`, `K_•` the Koszul complex of `x^{[q]}` over `R` with `K_i = R(−iq)^{\binom ni}`, `H_i = H_i(x^{[q]};R)`, `M^\vee = \mathrm{Hom}_K(M,K)` graded by `(M^\vee)_j = (M_{−j})^*`.
`R` is a graded CI, hence **Gorenstein**, `\dim R = k+1`, `a := a(R) = (k+1)^2 − (2k+2) = k^2−1`, `ω_R ≅ R(a)`.

## 2. The two inputs
**(I1) Every `H_i` has FINITE LENGTH.** `H_i` is annihilated by `(x^{[q]})`, so it is supported on `V(x^{[q]}) ∩ \mathrm{Spec}\,R`, which is the origin because `A` is Artinian. A finitely generated graded module supported at the irrelevant ideal is Artinian.
**(I2) Koszul self-duality.** `\mathrm{Hom}_R(K_i,R) = R(iq)^{\binom ni} = K_{n−i}(nq)`, hence `H^j(x^{[q]};R) ≅ H_{n−j}(x^{[q]};R)(nq)`.

## 3. The theorem
> ### **THEOREM.** For every `k ≥ 1`, every odd `q`, and **every `i`**:
> ### `H_{k+1-i}\big(x^{[q]};R\big) \;≅\; H_i\big(x^{[q]};R\big)^{\vee}\big(-a-nq\big)`, `a = k^2-1`, `n = 2k+2`.
> In particular (`i=0`) `H_{k+1} ≅ A^\vee(-a-nq)`, so `\dim_K H_{k+1} = A_k(q)`; and `\dim H_i = \dim H_{k+1-i}` for all `i`.

### 3.1 Proof — why the spectral sequence degenerates (the new mechanism)
Apply `\mathrm{Hom}_R(-,R)` to `K_•`. The hyper-Ext spectral sequence reads `E_2^{p,i} = \mathrm{Ext}^p_R(H_i(K_•),R) \Rightarrow H^{p+i}(\mathrm{Hom}_R(K_•,R))`.
By **(I1)** each `H_i` has finite length; and for a finite-length module `M` over a Gorenstein ring `R` of dimension `k+1`, local duality gives
`\mathrm{Ext}^p_R(M,R) = 0` for `p ≠ k+1`, and `\mathrm{Ext}^{k+1}_R(M,R) ≅ M^\vee(-a)`.
So `E_2^{p,i} = 0` unless `p = k+1`: **the sequence degenerates at `E_2`** and
`H^{k+1+i}(\mathrm{Hom}_R(K_•,R)) ≅ H_i^\vee(-a)`.
By **(I2)** the left side is `H_{n-k-1-i}(nq) = H_{k+1-i}(nq)`. Hence `H_{k+1-i}(nq) ≅ H_i^\vee(-a)`. ∎

> **Remark (why v1 was weaker).** v1 used only `\mathrm{grade}(x^{[q]},R) = k+1` and got `i=0`. The finite-length observation (I1) is what upgrades one case to all of them, because it makes the dualizing functor **exact** on the whole homology.

## 4. Two corollaries with teeth
> **C1 (Euler identity, exact).** `\sum_i (-1)^i \mathrm{HS}\big(H_i\big)(t) \;=\; \prod_{j}\big(1-t^{\deg e_j}\big)\cdot\big(1+t+\cdots+t^{q-1}\big)^{n}`.
> *(It is `\mathrm{HS}_R(t)\cdot(1-t^q)^n`; the factor `(1-t)^{-n}` cancels.)*
> **C2 (generators ↔ socle dictionary).** For graded modules `(M/\mathfrak m M)^\vee ≅ \mathrm{soc}(M^\vee)`. Combined with the Theorem:
> ### **the minimal generators of `H_i` correspond to the socle of `H_{k+1-i}`, under `d \longleftrightarrow (a+nq)-d`.**

## 5. Gate — `k=1`, `q=3` (prediction registered before computing)
Here `a = 0`, `n=4`, `a+nq = 12`, and `k+1-i = 2-i`, so `H_1` must be **self-dual**: `\dim(H_1)_d = \dim(H_1)_{12-d}`.
From C1 with `\chi(t) = (1-t)(1-t^3)(1+t+t^2)^4` and `H_0 = A`, `H_2 = A^\vee(-12)` (`HF(A_1(3)) = 1,3,6,6,3`):

| `d` | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|---|---|
| `\dim (H_1)_d` | 1 | 3 | 9 | 12 | 9 | 3 | 1 |

**Symmetric about `6` — verified.** `\dim H_1 = 38`, `\dim H_0 = \dim H_2 = 19 = A_1(3)`. Independently, `H_2` reproduced degree by degree in v1's gate, **6/6 byte-exact**.

## 6. Honest scope, and one route buried
**PROVED** `∀k ≥ 1`, `∀q` odd, char `≠ 2`, over any field. It does **not** prove `A_k(q) = P_k(q)`.
> ⛔ **Route buried (with its number).** «Bound `\mathrm{bottom\text{-}deg}\,H_k` to get the Degree Law» **cannot work**: `H_k ⊆ K_k` forces only `\mathrm{bottom\text{-}deg}\,H_k ≥ kq`, giving `\mathrm{top\text{-}deg}\,H_1 ≤ a+nq-kq`, which at `(1,3)` is **`9`** while the measured generation degree is **`5`**. Slack of four. The bound is on the top degree, not on generation.
> ### **The correct object is `\mathrm{soc}(H_k)`, by C2:** the Degree Law `\mathrm{gen\text{-}deg} ≤ q+2k` holds **iff** `\mathrm{soc}(H_k)` lives in degrees `≥ (a+nq)-(q+2k) = k^2-2k-1+(2k+1)q`.
> At `(1,3)` that threshold is **`7`**, and the socle of the self-dual `H_1` sits in degrees `\{7,8,9\}` with dimensions `\{3,3,1\}` — **equality, not slack.** The criterion is tight.

— **Bisel**, Chaise Longue campaign
