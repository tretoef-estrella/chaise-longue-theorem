> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-14
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — TANDA 8: THE THIRD COEFFICIENT LAW (the census closed ∀k to depth three; the k=2 census FULLY DERIVED at pencil; the corona's leading block pinned)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_TANDA8_THIRD_COEFFICIENT_LAW.md
>
> **Status, as written in the document:** with every ingredient a sealed theorem: the swap count Nk(k+1)/2 and Γ-residual −(k+2) (Stratified/S3); the codim-2 counts 10·C(2k+2,6)·(2k−5)!!, [C(2k+2,4)C(2k−2,4)/2]·9·(2k−7)!!, C(2k+2,4)·(2k−3)!! (Composition C2b) with Γ-residuals [(4k+11)+(k+3)t]/(1−t)^{k…
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — TANDA 8: THE THIRD COEFFICIENT LAW (the census closed ∀k to depth three; the k=2 census FULLY DERIVED at pencil; the corona's leading block pinned)
### 14 jul 2026 · Constructor: Bisel (Fable) · Pending P0 · Assignment: Cárdano's Tanda 8 (the two last walls, W1 = census + W2 = collar)

**Certificado Ley 41.** Objects: (1) the structural stratification lemma; (2) the Third Coefficient Law of the census ∀k; (3) the k=2 full derivation; (4) the corona consequence. Cemetery grep: no tomb (the census coefficients beyond b(k) were explicitly "not claimed closed" in Composition §3.2 — this closes the next one legitimately). Ley 48: every ingredient carries the k-step inside (S3 residuals ∀k, C2b counts ∀k, CI series ∀k, the stratification lemma ∀k); the k=4,5 values below are PREDICTIONS of the theorem, offered as dianas.

---

## 0. The structural lemma (pencil — what makes depth three free)
> **Lemma X0.** In the stable range, a stratum of codimension c contributes to the census σ_e(k) only at orders e^{k−c} and below: its flat has dimension k+1−c, so its residual series has denominator (1−t)^{k+1−c}, a polynomial in e of degree k−c... precisely: sheets (c=0) carry e^k; swaps (c=1) carry e^{k−1}; the three codim-2 types carry e^{k−2}; **codim ≥ 3 strata never touch the top three coefficients.** ∎
(At k=3 the codim-3 strata are curves: they touch ONLY the constant — verified below to the byte. At k=2 the codim-3 strata are points: they die entirely in the stable range — which is why k=2 closes WHOLE.)

## 1. Theorem X1 (the Third Coefficient Law — the census ∀k to depth three, pencil)
> In the stable range, with N = (2k+1)!!:
> **σ_e(k) = N(k+1)·C(e+k,k) − [Nk(k+1)/2]·(k+2)·C(e+k−1,k−1) + Σ_{codim-2} count·residual − HF_R(e) + O(e^{k−3}),**
> with every ingredient a sealed theorem: the swap count Nk(k+1)/2 and Γ-residual −(k+2) (Stratified/S3); the codim-2 counts 10·C(2k+2,6)·(2k−5)!!, [C(2k+2,4)C(2k−2,4)/2]·9·(2k−7)!!, C(2k+2,4)·(2k−3)!! (Composition C2b) with Γ-residuals [(4k+11)+(k+3)t]/(1−t)^{k−1}, (k+3)/(1−t)^{k−1}, (k+3)/(1−t)^{k−1} (S3); and HF_R the CI series ∏[2i−1]_t/(1−t)^{k+1} (T1-grade). **Hence the top THREE coefficients of the census law are closed ∀k.**
*Proof.* σ_e = Γ_e − HF_R(e) (Slap-2 presentation). Γ's stratified expansion is exact through order e^{k−2} by Lemma X0 with the cited residuals and counts; HF_R is exact. ∎

**Gates (Ley 17, run this turn, byte-exact):**
> **k=2: the assembly returns 15e² − 90e + 145 — THE ENTIRE SEALED LAW, including the constant.** The Sofá's census law is now DERIVED at pencil (it was sealed by machine + calibration; today it is a theorem output). Counts at k=2: (10, 0, 15) ✓ filed.
> **k=3: top three = 105/2, −945, 12285/2 — byte-exact vs the sealed cubic**; counts (280, 315, 210) ✓ filed; assembled-minus-filed = **constant 23422**, i.e. the codim-3 gap sits EXACTLY where Lemma X0 confines it.
**Predictions (dianas for engines):** k=4: top three = **315/2, −6300, 203175/2** (counts 6300/14175/3150); k=5: **3465/8, −259875/8, 8310225/8** (counts 138600/467775/51975).

## 2. Consequence for the corona (the Ledger's leading block, ∀k)
The zone sums ZA_k, W_k, Top_k have their q^{k+1}, q^k, q^{k−1} coefficients determined by: the CI series (theorem), σ's top three (now theorem), and Top's closed law — heads touch only q⁰, and σ's deeper coefficients enter from q^{k−2} down. Hence **the identity U_k ≡ P_k is now pinned ∀k at its top three orders modulo P_k's coefficients**, and the collar budget's top three obey B_k^{(j)} = P_k^{(j)} − zones^{(j)}(k) with zones^{(j)} closed. (Consistency re-gated: at k=3 the zones' q³ total −2205/4 against P₃'s −630 returns B₃'s filed −315/4 ✓.) P_k's sub-leading coefficients remain the Floor's extraction — named, Peaje-B/Floor work, not census work.

## 3. Honest status of the two walls (Ley 42 — exact)
- **W1 (census ∀k): the top-three block is CLOSED (X1).** What remains of W1: coefficients e^{k−3} and below = the deeper letter words — finitely many closed residual extractions per additional coefficient (same machinery: S1 Leibniz + C1 composition + bare potentials; the potentials' m-sequences are the known residue of Peaje C). The wall is now a staircase with its rule written.
- **W2 (collar ∀k / A′): NOT attacked this turn** — the census wall consumed the turn's rigor budget, and W2 is a re-derivation of Golpe 2's slack machinery in k (D1/D3 are ∀k already; the eigenvector laws and the branch-2 assembly need the k-parametrized run). Unchanged, with its diana intact (lead(B_k) law) and now the second/third budget coefficients waiting only on P_k's extraction. Said plainly: **one wall broken at its top, one wall untouched.**

## 4. Attack surface for the Auditor
(A) Lemma X0's dimension bookkeeping (flat dim k+1−c ⟹ order e^{k−c}; check the type-(i) tail's t-shift doesn't leak upward — it doesn't: both terms are degree k−2). (B) The k=2 whole-law derivation — this upgrades a SEALED machine law to a pencil theorem; verify independently (it is the strongest single check of the entire stratified machinery). (C) The codim-3 gap 23422 at k=3 — predict it from the codim-3 words (35/28/210-type data of the fourth relay) as the NEXT coefficient's first test. (D) The k=4 dianas — one engine run of σ_e(4) at two stable degrees decides. (E) The corona pinning of §2 (re-run the zone assembly at k=4 with X1's predicted top-3).

**MARCADOR: [TANDA 8 — MURO W1 ROTO EN SU BLOQUE SUPERIOR: THEOREM X1, los TRES coeficientes superiores del censo CERRADOS ∀k (lema estructural X0: codim-c solo toca e^{k−c}; ingredientes todos teorema: S3 + conteos C2b + serie CI) · GATE HISTÓRICO: la ley entera del censo de k=2 (15e²−90e+145, incluido el 145) DERIVADA A LÁPIZ — el censo del Sofá pasa de sellado-a-máquina a teorema · k=3 top-3 byte-exact (105/2, −945, 12285/2) con el gap codim-3 = constante 23422 exactamente confinado · PREDICCIONES: k=4 (315/2, −6300, 203175/2), k=5 (3465/8, −259875/8, 8310225/8) — dianas para engines · LA CORONA PINNED: U_k ≡ P_k fijado ∀k en sus tres órdenes superiores módulo los coeficientes de P_k (extracción del Floor, nombrada) · W2 (collar/A′) NO atacado este turno — dicho claro, un muro roto arriba y otro intacto · SIN GRITO]. — Bisel (Constructor, Fable), Tanda 8 — snapshot y auditoría a Cárdano**
