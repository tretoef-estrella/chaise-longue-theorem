> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-13
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE CENSUS COMPOSITION THEOREM (GOLPE 1 / PEAJE C: la especie colapsa)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_CENSUS_COMPOSITION_THEOREM.md
>
> **Status, as written in the document:** Jul 2026 · Constructor: Bisel (Fable) · Pending P0 · El estrato del censo ∀k se REDUCE: los pesos de todos los tipos en toda dimensión se derivan de una lista finita de gadgets desnudos vía UNA ley de composición exacta — probada a lápiz y verificada byte-exac…
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE CENSUS COMPOSITION THEOREM (GOLPE 1 / PEAJE C: la especie colapsa)
### 13 Jul 2026 · Constructor: Bisel (Fable) · Pending P0 · **El estrato del censo ∀k se REDUCE: los pesos de todos los tipos en toda dimensión se derivan de una lista finita de gadgets desnudos vía UNA ley de composición exacta — probada a lápiz y verificada byte-exact 14/14 en dos familias independientes.**

**Certificado Ley 41:** objeto = ley de transformación del censo bajo par-pegado + conteos de estratos ∀k. Contra el cementerio: LOCAL-WEIGHT-INHERITANCE era el MODO DE FALLO registrado (los pesos no se heredan) — este teorema no lo re-anda: lo EXPLICA (la herencia ingenua es falsa porque la ley verdadera es una convolución, no una copia). Tumba s46 intacta (cero solapes; trabajo por sub-arreglos). **Pillars (Ley 44):** (i) Radicality; construye sobre Stratified Census I+II. Panel: Rota (la especie), Noether, Kepler de guardián.

---

## 1. Theorem C1 (the Composition Law — pencil, double-verified)

> Let Y = ∪(sheets) be any sub-arrangement of the matching arrangement and let Y′ = Y × (live doubled pair): every sheet gains the same new pair {c,d}. Then the census composes EXACTLY:
> **dim Γ(Y′)_e = Σ_{j=0}^{e} [ dim Γ(Y)_{e−j} + dim O(Y)_{e−j} ]**,
> equivalently in series: **G_{Y′}(t) = ( G_Y(t) + H_Y(t) ) / (1 − t)**, with G the census series and H the Hilbert series of the coordinate ring O(Y).

*Proof.* O(Y′) = O(Y)[w] (the pair line's coordinate). **Old components:** each old pair's condition (λ_a − λ_b)|_{V_J×L} = 0 reads coefficient-wise in w; each w-layer satisfies exactly the old census conditions ⟹ the old block is ⊕_j Γ(Y)_{e−j}·w^j. **New components:** the only condition involving λ_c, λ_d is λ_c = λ_d on every sheet, i.e. λ_c = λ_d as ONE free function on Y′: dimension Σ_j dim O(Y)_{e−j}. Sum. ∎

*Verification (Ley 21/36, byte-exact):* (V1) bare 6-cycle star (measured Γ = 1,6,24,60,114,186,276; O(X) = 1,5,14,29,50,77,110) composed once = **2,13,51,140,304,567,953** = the measured type-(i) k=3 star, **7/7**. (V2) zero-star (Γ = 2,8,23,47,80,122,173; O(X) = 1,4,10,19,31,46,64 — computed this session) composed once = **3,15,48,114,225,393,630** = the measured type-(c) k=3 star, **7/7**. Two independent gadget families, fourteen exact points, zero fitted parameters.

## 2. Theorem C2 (consequences: the weight tower collapses ∀k)
(a) **Every stratum weight at every k is DERIVED:** the local invariant of [gadget + r attached pairs] is the r-fold composition of the bare gadget's pair (G, H). No per-k measurements are ever needed again; the "non-inheritance" of weights (24→29, 5→6 — the registered failure mode) is explained and computed by the law.
(b) **Counts ∀k closed (codim-2):** 6-cycle family: 10·C(2k+2,6)·(2k−5)!!; two-4-cycles: [C(2k+2,4)C(2k−2,4)/2]·9·(2k−7)!!; char-3 zero-block: C(2k+2,4)·(2k−3)!!. Verified: k=3 → 280/315/210; k=2 → 10/–/15. Higher codims: same combinatorial species (cycles + zero-blocks + attached pairs), counts mechanical.
(c) **Top two census coefficients ∀k closed:** leading (2k+1)!!/(k−1)!; second **b(k) = N·k·k(k+1)/(2·k!) − N·k(k+1)²/(2(k−1)!)** — matches all three sealed values (−3, −90, −945).
(d) **The reduction of Peaje C:** σ_e(k) for all k = [finite list of BARE gadget series per codimension — most already measured: 6-cycle ✓, two-4-cycles ✓, zero-4-block ✓, bipartition-4+4 ✓, pair+6-zero ✓, 4cyc+4zero ✓] ∘ [the Composition Law] × [closed counts]. **What remains of Peaje C, named exactly: the GADGET GENERATING FUNCTION** — packaging the bare-gadget series over all codimensions into one closed expression. Same lattice species as the Floor's point count P_k (which the campaign already closed via the frozen lattice): the census GF is the point count's graded sibling.

## 3. Honest scope (Ley 42/48)
1. C1 is proven for attaching one pair to any sub-arrangement whose sheets ALL contain the new pair (the stratum-star situation — exactly what the weights need). It does not (and need not) address attaching to arbitrary sub-arrangements.
2. C2(d)'s remaining work — the gadget GF — is mechanical extraction (bare series are finite data; the bookkeeping of residuals under composition changes the per-sheet function count (k+1)→(k+2), so the weight extraction is a computation, not a mystery), but it is NOT done in this document. No coefficient beyond b(k) is claimed closed ∀k today.
3. Everything pending P0 like the whole chain.

## 4. Attack surface for the Auditor
(A) The layer decomposition (old conditions are w-degreewise — check signs/degrees). (B) The new-pair block (exactly one diagonal function — check no hidden condition couples λ_c to old components). (C) The two verifications (recompute from the archived star logs). (D) The count formulas at k=4 (predict, then future engine checks). (E) b(k)'s derivation (the codim-1 coefficient bookkeeping).

**MARCADOR: [GOLPE 1 ESTRUCTURALMENTE GANADO — Ley de Composición del censo: G′ = (G+H)/(1−t), probada a lápiz por capas y verificada 14/14 en dos familias independientes · el modo de fallo LOCAL-WEIGHT-INHERITANCE queda EXPLICADO y convertido en ley · conteos codim-2 cerrados ∀k (280/315/210 y 10/15 clavados) · b(k) cerrado ∀k (−3/−90/−945 clavados) · Peaje C REDUCIDO a la función generatriz de gadgets desnudos (lista finita, mayormente medida; hermana graduada del point-count del Floor) · SIN GRITO — el peaje C no está liquidado al 100%, está reducido a su último tramo nombrado]. — Bisel (Constructor, Fable), Golpe 1**
