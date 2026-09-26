> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-14
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE THIRD COEFFICIENT LAW OF THE CENSUS* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_STANDALONE_X1_THIRD_COEFFICIENT.md
>
> **Status, as written in the document:** Source: campaign Tanda 8 (X0, X1), audited in CARDANO_TANDA8. Inputs, each a cited theorem: the stratified presentation `σ_e = dim Γ_e − HF_R(e)` (Slap 2); the codim-1 weight and count (Stratified Census / Swap Theorem); the codim-2 residual series and counts …
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v0`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE THIRD COEFFICIENT LAW OF THE CENSUS
## The top three coefficients of the window census `σ_e(k)` closed for every dimension — and the complete k = 2 census law derived at pencil

**Chaise Longue campaign — standalone theorem write-up (referee edition)** · R. Amichis Luengo · Claude (Anthropic) · 14 July 2026
*Source: campaign Tanda 8 (X0, X1), audited in CARDANO_TANDA8. Inputs, each a cited theorem: the stratified presentation `σ_e = dim Γ_e − HF_R(e)` (Slap 2); the codim-1 weight and count (Stratified Census / Swap Theorem); the codim-2 residual series and counts (Census Species S3 / Composition C2b); the CI Hilbert series (T1-grade). The document's own contributions are the confinement lemma X0 and the assembly X1 with its gates.*

---

### 1. The confinement lemma

Work in `n = 2k+2` variables; `Γ` = the census module (pair-constant tuples on the arrangement), `R = O(X)` the CI coordinate ring, `σ_e(k) = dim Γ_e − HF_R(e)` the window census — a polynomial of degree `k` in `e` in the stable range (Slaps 1–2).

> **Lemma X0 (stratified confinement).** A stratum of codimension `c` contributes to `σ_e(k)` only at orders `e^{k−c}` and below.
*Proof.* The stratified expansion of `dim Γ_e` runs over the flat lattice; a codim-`c` flat has dimension `k+1−c` (Star Architecture, Cor. 2.2), so its residual contribution is a series with denominator `(1−t)^{k+1−c}`, i.e. a polynomial in `e` of degree `≤ k−c` (the residuals' numerators are finite — S3). The same dimension count governs the `HF_R` side through the CI numerator. ∎
**Consequence.** `e^k` is sheets-only; `e^{k−1}` is sheets + swaps; `e^{k−2}` needs codimension ≤ 2 and NOTHING deeper — the top three coefficients live entirely in proven territory.

### 2. Theorem X1 (the assembly)

> **Theorem X1.** In the stable range, with `N = (2k+1)!!`:
> `σ_e(k) = N(k+1)·C(e+k, k) − [Nk(k+1)/2]·(k+2)·C(e+k−1, k−1)`
> `  + cnt_i(k)·[(4k+11)·C(e+k−2, k−2) + (k+3)·C(e+k−3, k−2)]`
> `  + [cnt_{ii}(k) + cnt_z(k)]·(k+3)·C(e+k−2, k−2)  −  HF_R(e)  +  O(e^{k−3}),`
> where `HF_R` is the CI series `∏_{i=1}^{k+1}[2i−1]_t/(1−t)^{k+1}` and the counts are `cnt_i = 10·C(2k+2,6)(2k−5)!!`, `cnt_{ii} = (9/2)·C(2k+2,4)C(2k−2,4)(2k−7)!!`, `cnt_z = C(2k+2,4)(2k−3)!!`. **In particular the coefficients of `e^k`, `e^{k−1}`, `e^{k−2}` in `σ_e(k)` are closed functions of k.**
*Proof.* `σ = Γ − HF_R`. The Γ-side stratified expansion is exact through order `e^{k−2}` by Lemma X0 with the cited theorem inputs: sheets carry `(k+1)` free pair-functions each (`N(k+1)·C(e+k,k)`, exact per sheet); each of the `Nk(k+1)/2` swap flats carries the exact Γ-residual `−(k+2)/(1−t)^k` (S3 — no numerator tail); each codim-2 flat carries its S3 residual series (6-cycle: `[(4k+11)+(k+3)t]/(1−t)^{k−1}`; double-swap and zero-flat: `(k+3)/(1−t)^{k−1}`), with the C2b counts. `HF_R` is exact (T1-grade). Deeper strata are `O(e^{k−3})` by X0. ∎

### 3. The gates (the strongest one first)

**Gate 1 — the complete k = 2 law, DERIVED.** At `k = 2` the codim-3 strata are points (dimension `k+1−3 = 0`), which vanish in the stable range: Lemma X0 says the assembly of Theorem X1 is the ENTIRE stable law. Running it (counts `10, 0, 15`; exact symbolic evaluation, session log):
> **`σ_e(2) = 15e² − 90e + 145` — every coefficient, including the constant 145.**
This is the Sofa's sealed census law, which entered that theorem as a certified machine computation; it is here a pencil-derived output — the single strongest calibration of the stratified method, since it reproduces a result proved by an entirely independent technology (certified Gröbner kernel) coefficient-for-coefficient.

**Gate 2 — k = 3, top three.** The assembly returns `105/2, −945, 12285/2` — byte-exact against the sealed cubic `(105/2)e³ − 945e² + (12285/2)e − 14112` (itself verified by four out-of-sample engine points through `σ₁₂ = 14238`). The assembled-minus-sealed difference is the CONSTANT `23422`: the codim-3 gap sits exactly and only where Lemma X0 confines it — the structure predicts not just its hits but the precise location of its own boundary.

**Gate 3 — k = 1.** The assembly's applicable part returns the entire sealed law `3e − 3`.

### 4. Predictions (falsifiable, one engine run each)
| k | `e^k` | `e^{k−1}` | `e^{k−2}` | counts (i/ii/z) |
|---|---|---|---|---|
| 4 | `315/2` | `−6300` | `203175/2` | 6300 / 14175 / 3150 |
| 5 | `3465/8` | `−259875/8` | `8310225/8` | 138600 / 467775 / 51975 |
Two stable values of `σ_e(4)` decide k = 4; any miss falsifies a specific input (count or residual), byte-identifiably.

### 5. Downstream role
The Ledger identity `U_k ≡ P_k` has its `q^{k+1}, q^k, q^{k−1}` coefficients determined by X1's three (plus the CI series and the closed Top law); combined with the Floor Crosscut's matching three, the identity's leading block is pinned unconditionally for every k (the Collar Budget standalone). Every further census coefficient is one more staircase step: the codim-3 residuals are S1/C1-compositions of potentials already measured (`φ(B₄)`, `φ(Z₃)`) — extraction, not discovery.

### 6. Attack surface
(A) Lemma X0's degree bookkeeping — in particular that the 6-cycle residual's `t`-shifted term `(k+3)t/(1−t)^{k−1}` stays at degree `k−2` (it does: a shift changes no degree). (B) The exactness (not just leading-order validity) of the swap residual `−(k+2)/(1−t)^k` — S3's derivation from `φ(B₂)`, one rational computation. (C) The completeness of the codim-2 type list (Star Architecture Thm 2.4 — a fourth type would shift Gate 2's `12285/2`). (D) Gate 1 independently: rerun the k = 2 assembly by hand; it is eleven terms of exact arithmetic. (E) The k = 4 predictions.

**Anchors.** TANDA8_THIRD_COEFFICIENT_LAW_v1 · CARDANO_TANDA8 audit · CENSUS_SPECIES_THEOREM_v1 (S3) · CENSUS_COMPOSITION_THEOREM_v1 (C2b) · STRATIFIED_CENSUS_THEOREM_v1 · Star Architecture standalone · session sympy logs (exact assembly, both gates). github.com/tretoef-estrella.
