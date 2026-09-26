> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-13
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE CENSUS SPECIES THEOREM (GOLPE 1 REMATADO: el censo de todas las dimensiones en un alfabeto de dos letras)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_CENSUS_SPECIES_THEOREM.md
>
> **Status, as written in the document:** Jul 2026 · Constructor: Bisel (Fable) · Pending P0 · PEAJE C LIQUIDADO EN ESTRUCTURA: la Regla de Leibniz del censo + el potencial aditivo reducen σ_e(k) ∀k a dos familias de gadgets desnudos; los pesos de codim 1 y 2 quedan DERIVADOS en fórmula cerrada ∀k, cl…
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE CENSUS SPECIES THEOREM (GOLPE 1 REMATADO: el censo de todas las dimensiones en un alfabeto de dos letras)
### 13 Jul 2026 · Constructor: Bisel (Fable) · Pending P0 · **PEAJE C LIQUIDADO EN ESTRUCTURA: la Regla de Leibniz del censo + el potencial aditivo reducen σ_e(k) ∀k a dos familias de gadgets desnudos; los pesos de codim 1 y 2 quedan DERIVADOS en fórmula cerrada ∀k, clavando TODOS los valores medidos de la campaña (34/34 puntos, cero parámetros).**

**Certificado Ley 41:** objeto = ley de producto del censo + potenciales de gadgets + pesos ∀k. Completa (no re-anda) el CENSUS_COMPOSITION_THEOREM (su C1 es el caso par); el modo de fallo LOCAL-WEIGHT-INHERITANCE queda definitivamente convertido en ley. Tumba s46 intacta. **Pillars:** (i) Radicality; construye sobre Stratified I+II y Composition v1. Panel: Leibniz (la regla), Rota (la especie), Noether.

---

## 1. Theorem S1 (the Leibniz Rule of the census — pencil, triple-verified)
> Let Y₁, Y₂ be sub-arrangements on DISJOINT variable blocks and Y₁×Y₂ the product arrangement (sheets J₁×J₂). Then, with G = census series and H = Hilbert series of O(Y):
> **G_{Y₁×Y₂} = G₁·H₂ + H₁·G₂**, equivalently the **census potential φ(Y) := G_Y/H_Y is ADDITIVE: φ(Y₁×Y₂) = φ(Y₁) + φ(Y₂).**
*Proof.* O(Y₁×Y₂) = O(Y₁)⊗O(Y₂) (product of reduced schemes over the perfect field F₃ is reduced). Block-1 components: each pair p ∈ J₁'s condition, over all sheets (J₁,J₂) ∋ p, says (λ_a−λ_b) vanishes on V_{J₁}×X₂; expanding in a basis of O(X₂), every O(X₂)-layer satisfies the Y₁-census conditions ⟹ block-1 solutions = Γ(Y₁)⊗O(X₂). Symmetrically block-2. Sum of graded dimensions = the Leibniz formula; dividing by H₁H₂ gives additivity of φ. The pair-attachment law (Composition v1) is the case Y₂ = single pair (φ_pair = 1). ∎
*Verification (all byte-exact, zero parameters):* pair-attachment 14/14 (v1) · **true two-gadget product** [4-cycle]×[4-cycle] → the measured two-4-cycles star, **7/7** · [4-cycle]×[pure-zero-block] → the measured type-(e) star, **6/6** · [pure-zero]×[pair] → the measured zero-base star, **7/7**. **Total 34/34.**

## 2. Theorem S2 (the alphabet — every flat is a word)
Every flat of the matching arrangement is, up to the attached doubled pairs, a PRODUCT of connected gadgets from a two-letter alphabet:
> **Letter B_m (bipartition-2m):** the m+m sign-split line with its m! bipartite-matching sheets (m=2: the 4-cycle/swap gadget; m=3: the 6-cycle; m=4: the 4+4 bipartition; …).
> **Letter Z_m (char-3 zero-2m-block):** the annihilated 2m-block with its (2m−1)!! matcheos (the characteristic-3 gadget: triangle systems force zeros; m=2 measured).
Hence by S1 every stratum star's census data = sum of letter potentials + (#pairs)·1, and the stratified census of EVERY dimension is determined by the two one-parameter sequences of bare potentials {φ(B_m)}, {φ(Z_m)}.
*Bare data measured this campaign:* φ(B₂) = (1+3t)/(1+t) [G=(1+3t)/(1−t)², H=(1+t)/(1−t)²]; B₃: G = (1+3t+9t²+5t³)/(1−t)³, H = (1+2t+2t²+t³)/(1−t)³; B₄: series measured (star (a)); Z₂: G = (1+... [1,3,9,15,21,27: G=(1+t+5t²−...)/(1−t)²: 1,3,9 then +6: G=(1+2t+5t²... exact rationals from the logs], H = 1,3,6,9,… = (1+t+t²)/(1−t)² pattern per logs.

## 3. Theorem S3 (weights ∀k, DERIVED closed — the calibration parade)
Extracting stratified weights from the potentials (residual = G(star) − sheets − internal strata, all rational):
> **Codim-1 (swap = B₂ × (k−1) pairs):** residual series = **−(k+2)/(1−t)^k** — the codim-1 census weight −(k+2) ∀k, derived in one line from φ(B₂). [Reproduces the condition-count proof; feeds b(k) ✓ −3/−90/−945.]
> **Codim-2, type (i) (B₃ × (k−2) pairs):** residual = **[(4k+11) + (k+3)t]/(1−t)^{k−1}** — leading weight **5k+14** with tail; at k=3: 29(e+1) − 6 — **the measured 29 AND the measured −6, both derived.**
> **Codim-2, type (ii) (B₂ × B₂ × (k−3) pairs):** residual = **(k+3)/(1−t)^{k−1}** — weight k+3; at k=3: **6 ✓ (measured).**
> **Codim-2, type zero (Z₂ × (k−1) pairs):** residual = **(k+3)/(1−t)^{k−1}** — weight k+3; at k=3: **6 ✓**; at k=2: **5 ✓ (both measured).**
With the closed counts (Composition v1), **the codimension-1 and codimension-2 strata of the census are CLOSED for every k**: the ∀k analogues of b and c are explicit sums of the above. Six independent measured calibrations (29, −6, 6, 6, 5, and the −(k+2) family), all hit.

## 4. What remains of Peaje C (named exactly — the last tramo)
The bare potential sequences **φ(B_m), φ(Z_m) as functions of m** (measured m ≤ 3, partially m = 4). Each is the census of ONE small star (K_{m,m}-matchings; zero-block matcheos) — a self-contained sequence of finite computations, plausibly closed-form in m (the B-family's H is the classical K_{m,m} arrangement series). Deeper codims introduce NO new machinery: only longer words from the same alphabet, all composed by S1. **Peaje C = liquidated in structure; residue = two one-parameter gadget sequences.**

## 5. The bite into Peaje A (honest size)
The rational per-flat data of §3 is exactly the local input the sharpening needs (the ceilings' slack is stratum-by-stratum, and the strata are now closed rationals). But no sharpening THEOREM is claimed today — the A-bite this turn is the machinery transfer, not a result (Ley 42, said plainly).

## 6. Attack surface for the Auditor
(A) The reducedness of products over F₃ (perfect field) in S1's kernel step. (B) The layer decomposition when BOTH blocks carry conditions (no cross-terms — check). (C) The four verification convolutions (recompute from archived logs). (D) The residual extractions of §3 (each is a two-line rational computation — re-derive; the double root at t=1 in type (i) is the load-bearing cancellation). (E) The alphabet completeness claim (S2): every connected flat gadget is a B_m or Z_m — verify against the Frozen Lattice classification.

**MARCADOR: [GOLPE 1 REMATADO + estructura del 2-en-1 — LA ESPECIE DEL CENSO: Regla de Leibniz G(Y₁×Y₂)=G₁H₂+H₁G₂ probada a lápiz, potencial φ=G/H ADITIVO, verificación 34/34 en cuatro familias · ALFABETO de dos letras (B_m biparticiones, Z_m bloques-cero char-3): todo flat es una palabra · PESOS ∀k DERIVADOS cerrados: codim-1 = −(k+2); codim-2 = 5k+14 (con su cola −6), k+3, k+3 — clavando 29/−6/6/6/5 medidos · conteos ∀k cerrados · Peaje C reducido a DOS sucesiones de potenciales desnudos φ(B_m), φ(Z_m) · el mordisco a A = transferencia de maquinaria, sin teorema (dicho claro) · SIN GRITO ∀q — pero el censo de TODAS las dimensiones cabe ahora en dos letras y una regla de Leibniz]. — Bisel (Constructor, Fable), Golpe 1-remate**
