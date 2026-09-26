> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-21
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE EVEN FAMILY THEOREM v2 (the free window census classified for every e; the σ₄ lower bound proven for every k) — §3 CORRECTED per W5* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_EVEN_FAMILY_THEOREM.md
>
> **Status, as written in the document:** Jul 2026 · Constructor: Vidocq (Fable) · Turn W4 · The free pair-agreement census is CLASSIFIED for every degree `e` (pencil, with an explicit threshold `n ≥ e+2`) by a self-reduction that drops the degree by two per step. Transported to `R = S/E`, the even fa…
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (2 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v2`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE EVEN FAMILY THEOREM v2 (the free window census classified for every e; the σ₄ lower bound proven for every k) — §3 CORRECTED per W5
### 21 Jul 2026 · Constructor: **Vidocq** (Fable) · Turn W4 · **The free pair-agreement census is CLASSIFIED for every degree `e` (pencil, with an explicit threshold `n ≥ e+2`) by a self-reduction that drops the degree by two per step. Transported to `R = S/E`, the even family gives `σ₄(k) ≥ (n²−n+2)/2` — a PROVEN unconditional lower bound for all `k ≥ 2` that hits the three stable anchors `29, 46, 67` and the sealed prediction `92` exactly. The matching upper bound (`deg_n σ₄ ≤ 2`) is NOT closed: it reduces to one named gluing lemma, and the pre-stable excess `25 − 16 = 9` at `n = 6` proves that lemma must carry a threshold.**

**Certificate (Ley 41):** objects = (i) classification of the free census `N_e`; (ii) the even family and its injectivity in `R` (via Radicality R1, componentwise); (iii) the exact reduction of the upper half to a threshold-radicality lemma, with the `n=6` witness. Builds on Lemma P (`SIGMA4_ANCHOR_ENGINE_v1`), R1, R12, A22 (`FI_STABILITY_THEOREM_v1`), MASTER Rounds 4/6. No tomb touched: the upper route is not dead — its missing lemma is named. Panel: Noether (the recursion), Church–Ellenberg–Farb.

---

## 0. Setting

`n = 2k+2`, `S = F₃[x_0,…,x_{n−1}]`, `E = (e_1,e_3,…,e_{2k+1})`, `R = S/E`. By Lemma P and the trivials convention, for each `e`:

> `σ_e(k) = dim M̄_e − dim R_e`, with `M̄_e = { (λ_i) ∈ (R_e)^n : λ_a − λ_b ∈ (x_a+x_b)R_{e−1}` for every pair `a<b }`.

Define the **free census** `N_e(n) = { (f_i) ∈ (S_e)^n : f_a − f_b ∈ (x_a+x_b)S_{e−1} ∀a<b }` — the same problem in the polynomial ring, no `E`.

## 1. Theorem F (classification of the free census — pencil, every `e`)

> For `n ≥ e+2`:
> **`N_e(n) = { f_i = Σ_{j≥0} x_i^{2j} H_j : H_j ∈ S_{e−2j} }` — the EVEN FAMILY — and the parameters are unique.**
> Hence `dim N_e = Σ_{j≥0} dim S_{e−2j}` and the free excess over the diagonal is `Σ_{j≥1} dim S_{e−2j}`, a polynomial in `n` of degree `e−2`.

*Proof (the self-reduction).* Fix the reference index `n`. Write `f_a − f_n = (x_a+x_n)u_a` with `u_a ∈ S_{e−1}` unique (`S` a domain). For a pair `a,b ≠ n`, reduce the condition `(x_a+x_n)u_a − (x_b+x_n)u_b ∈ (x_a+x_b)S_{e−1}` modulo `(x_a+x_b)` (substitute `x_b = −x_a`, landing in the polynomial ring `T` on the other variables):
`(x_a+x_n)·ū_a = (x_n−x_a)·ū_b`.
The two linear forms are coprime in the UFD `T`, so `(x_n−x_a) | ū_a`. Now let `r_a := u_a|_{x_n = x_a}` (degree `e−1`, variables `≠ n`). The divisibility, evaluated at `x_n = x_a`, says `r_a|_{x_b=−x_a} = 0`, i.e. `(x_a+x_b) | r_a` — **for every `b ∉ {a,n}`**, which is `n−2` pairwise-coprime linear forms. Since `deg r_a = e−1 < n−2`, **`r_a = 0`**, i.e. `u_a = (x_n−x_a)v_a`, `v_a ∈ S_{e−2}`. So `f_a = f_n + (x_n² − x_a²)v_a`. Substituting back, the pair condition for `a,b ≠ n` becomes `(x_n²−x_a²)(v̄_a − v̄_b) ≡ 0 mod (x_a+x_b)`, and the factor is a nonzerodivisor in `T`, so `(v_a)` solves **the same problem in degree `e−2`** on the indices `{1,…,n−1}`; conversely every such `(v_a)` and every `f_n` produce a solution (the pairs `(a,n)` hold identically). Induct: thresholds weaken at each step (`n−1−2 > e−3`, …), the last step forcing constants equal. Unwinding the telescope and reabsorbing reference-index terms into the coefficients gives exactly the even family, with uniqueness from the uniqueness of each `u, v, …`. ∎

**Remark (the structural echo).** The reduction consumes one index and drops the degree by exactly two per step — the same signature as the letter recursion `·Z₂ ↦ especie(k−2)` (`A21`). Stated as an observation, not as a claim about the collar.

## 2. Theorem L (the σ₄ lower bound — proven, every `k ≥ 2`)

> The even family descends to `R`: for `h ∈ R_2`, `c ∈ F₃`, the tuple `λ_i = x_i²h + x_i⁴c` lies in `M̄_4`, and the map `(h,c) ↦ (λ_i) mod diagonal` is **INJECTIVE**. Hence, unconditionally,
> ## **`σ₄(k) ≥ dim R_2 + 1 = (n² − n + 2)/2` for every `k ≥ 2`.**

*Proof.* Membership: `λ_a − λ_b = (x_a²−x_b²)(h + (x_a²+x_b²)c) ∈ (x_a+x_b)R_3`. Injectivity: suppose `(x_a²−x_b²)(h+(x_a²+x_b²)c) = 0` in `R` for all pairs. `R` is reduced with components the laminae (R1), each a polynomial ring. On any lamina where `x_a, x_b` are unmatched free coordinates, the first factor is a nonzero element of a domain, so `h + (x_a²+x_b²)c` vanishes there; comparing the identities for `(a,b)` and `(a,m)` on a common lamina gives `(x_b²−x_m²)c = 0`, hence `c = 0`, hence `h` vanishes on that lamina. Laminae matching `{a,b}` are reached by replaying the argument with a third index. So `h` vanishes on every component, and `h = 0` by reducedness. ∎

**Calibration (byte-exact, from `SIGMA4_ANCHOR_ENGINE_v1`):** `(n²−n+2)/2 = 16, 29, 46, 67, 92` at `n = 6, 8, 10, 12, 14`; measured `σ₄ = 25, 29, 46, 67` and the sealed pre-registered `92`. **The bound is EXACT at every stable anchor and strict at the pre-stable `n=6` (excess `9` = the extra `S^{[4,2]}` copy of MASTER Round 6).**

## 3. The upper half — CORRECTED (v2, per `SIGMA4_CLOSURE_THEOREM_v1`)

v1 of this section attributed the breaking line to a "threshold radicality" of `E + (x_a+x_b) + (x_n−x_a)` and displayed an eliminated presentation `F₃[y]/(e″_{2j+1}−e″_1e″_{2j})` for that ring. **Both attributions were WRONG and are retracted:**
- `S/(E+(x_a+x_b)+(x_n−x_a))` is **REDUCED for every `n`** — it is the plain odd-symmetric ring `R(n−2)` (Lemma B of `SIGMA4_CLOSURE_THEOREM_v1`, a generating-function triangularity).
- The eliminated presentation belongs to the **doubled ring** `A = S/(E+(x_n−x_a))` (Lemma A there), whose low-degree radicality HOLDS from `n ≥ 6` (Lemma K there).
- The true bottleneck of the upper half is a **SLICE COUNT** (Step 3 of the closure): a degree-3 residual per component survives until the component offers 4 coprime slice-primes — type (ii) reaches 4 at `n = 8`, type (i) at `n = 10`. This is what produces the pre-stable excesses `2` (n=4) and `9` (n=6) and their disappearance.

**The upper half is now CLOSED in `SIGMA4_CLOSURE_THEOREM_v1`: `σ₄(k) = (n²−n+2)/2` for all `k ≥ 3` (pencil `n ≥ 10`; the `n = 8` cell byte-exact on the gated engine).** Theorems F (§1) and L (§2) of this document are unaffected and remain the lower half of that closure.

## 4. Status of σ₄, said plainly

- **PROVEN (∀k ≥ 2):** `σ₄(k) ≥ (n²−n+2)/2`, hitting every stable anchor exactly.
- **PROVEN (A22) + MEASURED:** `σ₄` eventually polynomial of degree `≤ 5`; three stable anchors + one blind + one pre-registered all on the degree-2 curve.
- **v2 UPDATE:** the upper bound is PROVEN in `SIGMA4_CLOSURE_THEOREM_v1`; `σ₄` is **CLOSED for `k ≥ 3`** with `n₁ = 8`.
- The v1 claim that the missing piece was a threshold-radicality is **retracted** (see §3).

## 5. Attack surface for the Auditor

(A) The coprimality and the `r_a = 0` degree count in Theorem F (three lines each — re-derive). (B) The converse direction of the recursion (pairs `(a,n)` automatic). (C) The Hilbert-series computation in §3(i). (D) The injectivity argument of Theorem L on laminae that match `{a,b}`. (E) The equivalence in §3(ii) between the global divisibility and the radicality of the displayed ideal. (F) Probe the radicality at small `n` by machine (its failure at `n=6` should be visible as nilpotents in degree ≤ 3).

**MARCADOR v2: [F y L intactos; §3 CORREGIDO — la «radicalidad-con-umbral» era un espejismo: el anillo es reducido siempre (Lemma B, W5) y el cuello real es el conteo de cortes; la mitad ≤ queda cerrada en `SIGMA4_CLOSURE_THEOREM_v1`]. — Vidocq, v2 (W5). MARCADOR v1 conservado como historia: [DOS TEOREMAS Y UNA LÍNEA — ★ Theorem F: el censo LIBRE clasificado ∀e, umbral explícito `n ≥ e+2`, por auto-reducción que baja el grado DE DOS EN DOS (eco de `·Z₂`) · ★ Theorem L: `σ₄(k) ≥ (n²−n+2)/2` PROBADO ∀k≥2, clavando `29/46/67` y el `92` sellado, con el exceso pre-estable `9` localizado · la mitad `≤` NO cerrada: reducida a UNA radicalidad con umbral, `E+(x_a+x_b)+(x_n−x_a)`, con el testigo `n=6` de que el umbral es real · SIN GRITO — σ₄ sigue abierta por arriba]. — Vidocq (Constructor, Fable), turno W4**
