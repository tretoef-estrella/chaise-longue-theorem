> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-25
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE GORENSTEIN–KOSZUL DUALITY THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_GORENSTEIN_KOSZUL_DUALITY_THEOREM.md
>
> **Status, as written in the document:** (F2) `A` is Artinian, so `\mathrm{ht}(x^{[q]}R) = k+1 = \dim R`; `R` is CM, hence `\mathrm{grade}(x^{[q]},R) = k+1`. Consequently `H_i = 0` for `i > n − (k+1) = k+1`, and `H^i(x^{[q]};R) = 0` for `i < k+1` with `H^{k+1}(x^{[q]};R) ≅ \mathrm{Ext}^{k+1}_R(A,R)`.
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE GORENSTEIN–KOSZUL DUALITY THEOREM
### The top Koszul homology of the Frobenius power over `R = S/E` is the Matlis dual of `A` itself — so `A_k(q)` is a Koszul homology dimension, and the socle of `A` is its bottom graded piece
### Constructor: **Bisel** · 25 August 2026 · Pending P0 · char `K ≠ 2`, `q` odd

**Certificado Ley 41 (corrido ANTES de escribir).** Object: the graded Koszul homology `H_•(x^{[q]};R)` of the Frobenius power over the odd-elementary complete intersection, and its duality. Cemetery grep by object: `DEFECT_TOR_LOCALIZATION_THEOREM_v1` computes the **defect** as a `\mathrm{coker}` of `\operatorname{Tor}_1` and records `\operatorname{Tor}_i(M,B)=H_i(x^{[q]};M)`; it does **not** state a duality, does not identify any `H_i` with `A^\vee`, and does not use the Gorenstein property of `R`. `CASCADE_COLLAPSE` works **per sheet** (`O(V_J)`), not over `R`. No tomb shares this object. **Pillars (Ley 44):** (i) Odd Symmetric (`E` is a radical CI); (ii) Point-Count (via `A_k(q)`).

---

## 1. Setting
`K` a field, `\mathrm{char}\,K ≠ 2`; `q` odd; `k ≥ 1`, `n = 2k+2`; `S = K[x_0,…,x_{n−1}]`;
`E = (e_1,e_3,…,e_{2k+1})` the **odd** elementary symmetric polynomials — a homogeneous **complete intersection** of degrees `1,3,…,2k+1` (`ODD_ELEMENTARY_CI_THEOREM`, PROVED `∀k`);
`R := S/E`; `x^{[q]} := (x_0^q,…,x_{n−1}^q)`; `A := R/(x^{[q]})R = S/(E+m^{[q]})`;
`K_•` the Koszul complex of `x^{[q]}` over `R`, `K_i = R(−iq)^{\binom{n}{i}}`; `H_i := H_i(x^{[q]};R)`.
For a graded Artinian `A`, `A^\vee := \mathrm{Hom}_K(A,K)` with `(A^\vee)_j = (A_{−j})^*`.

## 2. Three standard facts, recorded with their reasons
**(F1)** `R` is a graded **complete intersection**, hence **Gorenstein**, of dimension `n − (k+1) = k+1`, with `a`-invariant
`a(R) = \sum_j \deg e_j − n = (1+3+\cdots+(2k+1)) − (2k+2) = (k+1)^2 − (2k+2) = k^2 − 1`, and `ω_R ≅ R(a(R))`.
**(F2)** `A` is Artinian, so `\mathrm{ht}(x^{[q]}R) = k+1 = \dim R`; `R` is CM, hence `\mathrm{grade}(x^{[q]},R) = k+1`. Consequently `H_i = 0` for `i > n − (k+1) = k+1`, and `H^i(x^{[q]};R) = 0` for `i < k+1` with `H^{k+1}(x^{[q]};R) ≅ \mathrm{Ext}^{k+1}_R(A,R)`.
**(F3)** The Koszul complex is **self-dual**: `\mathrm{Hom}_R(K_i,R) = R(iq)^{\binom{n}{i}} = K_{n−i}(nq)`, hence `H^i(x^{[q]};R) ≅ H_{n−i}(x^{[q]};R)(nq)`.

## 3. The theorem
> ### **THEOREM.** For every `k ≥ 1` and every odd `q`,
> ### `H_{k+1}\big(x^{[q]};R\big) \;≅\; A^{\vee}\big(-a(R)-nq\big)`, with `a(R)=k^2−1`, `n=2k+2`.

**Proof.** By (F3) with `i = k+1` and `n−i = k+1`: `H^{k+1} ≅ H_{k+1}(nq)`. By (F2), `H^{k+1} ≅ \mathrm{Ext}^{k+1}_R(A,R)`. By (F1), `R ≅ ω_R(−a)`, so `\mathrm{Ext}^{k+1}_R(A,R) ≅ \mathrm{Ext}^{k+1}_R(A,ω_R)(−a)`; and since `\dim A = 0` and `\dim R = k+1`, local duality gives `\mathrm{Ext}^{k+1}_R(A,ω_R) ≅ ω_A`, which for a graded Artinian ring is `A^\vee`. Combining, `H_{k+1}(nq) ≅ A^\vee(−a)`, i.e. `H_{k+1} ≅ A^\vee(−a−nq)`. ∎

## 4. Consequences
> **C1.** `\dim_K H_{k+1}(x^{[q]};R) = \dim_K A = A_k(q)`. **The quantity of the conjecture is a Koszul homology dimension.**
> **C2.** `\big(H_{k+1}\big)_j ≅ \big(A_{\,a+nq-j}\big)^*`; hence `H_{k+1}` is concentrated in `\;(k+1)(k+q) \;≤\; j \;≤\; k^2−1+(2k+2)q`, the two ends being `\dim A_T` and `\dim A_0 = 1`.
> **C3.** Its **lowest** graded piece has dimension `\dim A_T = \dim\mathrm{soc}(A)` — and a graded module's lowest piece consists entirely of minimal generators. **This is the structural source of the measured multiplicities `3, 15, 91` at `k=1,2,3` (`q=3`), where `91` distinguishes `\dim A_T` from `(2k+1)!! = 105`.**
> **C4 (Poincaré pairing).** The multiplication of the Koszul homology algebra gives `H_i × H_{k+1−i} → H_{k+1} ≅ A^\vee(−a−nq)`, so `H_i ≅ (H_{k+1−i})^\vee(−a−nq)` whenever the pairing is perfect; in particular `\dim H_i = \dim H_{k+1−i}` and `\mathrm{top\text{-}deg}\,H_i = (a+nq) − \mathrm{bottom\text{-}deg}\,H_{k+1−i}`.

## 5. Gate — prediction registered BEFORE the computation
`k=1`, `q=3`, `n=4`, `a(R)=0`: the theorem predicts `H_2` concentrated in degrees `8..12` with dimensions `\dim A_{12−j}`, i.e. `(3,6,6,3,1)` from the archived `HF(A_1(3)) = (1,3,6,6,3)`, summing to `19 = A_1(3)`.
**Computed** (own code, `F_3`, `H_2 = \ker d_2/\mathrm{im}\,d_3` degree by degree):

| degree `j` | 8 | 9 | 10 | 11 | 12 | 13 |
|---|---|---|---|---|---|---|
| predicted | 3 | 6 | 6 | 3 | 1 | 0 |
| **measured** | **3** | **6** | **6** | **3** | **1** | **0** |

**6/6, byte-exact; total `19 = A_1(3)`.** The prediction was printed before the computation ran.

## 6. Honest scope
The theorem is **PROVED** for all `k ≥ 1` and all odd `q`, char `≠ 2`, over any field, from (F1)–(F3). **C4 is stated with its hypothesis** (perfectness of the pairing) and is **not** used elsewhere without saying so. **What this does NOT do:** it does not prove `A_k(q) = P_k(q)`, and it does not by itself give the sharp generation bound `q+2k` of the Degree Law — the duality bounds `\mathrm{top\text{-}deg}\,H_1` by `a+nq−\mathrm{bottom\text{-}deg}\,H_k`, which at `(1,3)` gives `9` where the measured generation degree is `5`. **The sharp bound needs `\mathrm{bottom\text{-}deg}\,H_k`, and that is the named next target.**

— **Bisel**, Chaise Longue campaign
