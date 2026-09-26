> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-14
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — TANDA 4: THE NERVE THEOREMS (S1-global verified E ≡ 0 in four letters; the star architecture, Künneth, and codimension induction proven; the residue pinned to the deepest flat)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_TANDA4_NERVE_THEOREMS.md
>
> **Status, as written in the document:** S1-global ⟺ E = 0, and by W3 this is now ONE statement: E vanishes at the deepest flat. For B_m the deepest flat is a line, so E ≠ 0 would contribute a nonzero tail to C − rank(ob) in every large degree — the four-letter data shows zero in EVERY degree. Status…
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — TANDA 4: THE NERVE THEOREMS (S1-global verified E ≡ 0 in four letters; the star architecture, Künneth, and codimension induction proven; the residue pinned to the deepest flat)
### 14 jul 2026 · Constructor: Bisel (Fable) · Pending P0 · Assignment: Cárdano's Tanda 4 (the golden egg: S1-global)

**Certificado Ley 41.** Objects: (1) the middle-homology module E := ker(ob)/im(φ); (2) the star architecture of letter flats; (3) Künneth for the defect complex; (4) the codimension induction. Cemetery grep: no tomb. Failure modes: ALIAS-CHAIN guarded (E is evaluated on anchors: four letters, every degree, byte-exact); Kepler: the induction carries the m-step inside; the residue is named, not blurred. Builds on: TANDA3 (L1/L2, ratified), TANDA2 (Golden Reduction, ratified), CENSUS_COMPOSITION/SPECIES (layer technique), T1 (CI structure).

---

## 0. The probe that decides (Ley 17): E ≡ 0 — S1-global holds byte-exact in every measured instance
The obstruction map ob: T → P = ⊕_F O(F)^{m−1} was implemented exactly (shared-pair functionals + sign-matched cycle functionals; flat parametrizations solved over F₃), and rank(ob_e) compared against C_e degree by degree:
> **B₂: E = 0 (6 degrees) · B₃: E = 0 (7 degrees) · Z₂: E = 0 (6 degrees) · Z₃: E = 0 (7 degrees).**
Four letters, every computed degree, E = C − rank(ob) ≡ 0 EXACTLY. (B₂/Z₂ were already proven identifications; B₃/Z₃ are the new deciding instances.) **The B₄ run did not complete in-session** (row-construction process died; the script is left reproducible in /home/claude/tanda1/) — named as the pending fifth check, not claimed (Ley 42).

## 1. Theorem W1 (the Star Architecture — pencil)
> Let G be a flat of codimension c of a letter arrangement. The sheets containing G form the star of G, and: (B_m) if G collapses the coordinates into blocks of sizes b₁,…,b_r, the star is σ·(S_{b₁}×⋯×S_{b_r}) — the product word **B_{b₁} × ⋯ × B_{b_r} × (shared pairs)**; (Z_m) the star of a flat is likewise a product word of smaller Z- and B-blocks and shared pairs. Moreover, the localization of the defect complex (F → T → P) at a generic point of G is the defect complex of the star (sheets not through G die in the localization; P's flat factors through G survive).
*Proof.* Membership ρ ⊇ G forces ρ to match σ outside the collapsed blocks (generic distinct values) and to be arbitrary inside each block — the Young-subgroup computation done for c = 1 and the 3-cycle case in Tanda 3, verbatim in general. Localization: O(V_ρ) localizes to 0 at G for ρ ⊉ G. ∎

## 2. Theorem W2 (Künneth/Leibniz for the defect complex — pencil)
> For arrangements Y₁, Y₂ on disjoint variable blocks, the defect complex of Y₁ × Y₂ is the totalization of the tensor product of the factors' complexes, and consequently **E(Y₁ × Y₂) = 0 whenever E(Y₁) = E(Y₂) = 0.** The pair-attachment case (Y₂ = doubled pair) is the Composition Law's layer decomposition at the defect level.
*Proof.* O of the product is the tensor of the factors' O's (reducedness over the perfect field — the Species Theorem's kernel step); each block's pair conditions and flat functionals read layer-by-layer in a basis of the other block's coordinate ring — the SAME layer decomposition proven in CENSUS_COMPOSITION C1 and SPECIES S1, applied now to all three terms of the complex simultaneously. Künneth over the field kills the middle homology of the totalization when both factors' vanish. ∎

## 3. Theorem W3 (the codimension induction — pencil, the m-step inside)
> **E(B_m) and E(Z_m) are supported on the single deepest flat** (the diagonal line for B_m; the minimal flat for Z_m).
*Proof.* Induction on m. E is supported on codim ≥ 2 flats (Tanda 3, L2c). Let G be any such flat that is NOT the deepest. By W1 its star is a product word of letters of sizes < m and shared pairs; by induction (base: L1, the 2-sheet local model, proven in Tanda 3) each factor has vanishing E; by W2 the word has vanishing E; by W1's localization statement, E localizes to 0 at G. Only the deepest flat — whose star is the whole letter, where induction cannot bite — can support E. ∎

## 4. The last inch, named exactly (Ley 42)
S1-global ⟺ E = 0, and by W3 this is now ONE statement: **E vanishes at the deepest flat.** For B_m the deepest flat is a line, so E ≠ 0 would contribute a nonzero tail to C − rank(ob) in every large degree — the four-letter data shows zero in EVERY degree. Status: the vanishing is pencil-reduced to a single localized statement, instance-verified wherever measured, not yet proven ∀m. Candidate kill mechanisms for the relay: (a) Peskine–Szpiro acyclicity on 0→Q→T→P — needs depth Q ≥ 2 (Q torsion-free gives ≥ 1; one more step); (b) the cone-off over the nerve using O(V_J) ↠ O(V_J∩V_{J₀}) (all sheets share the deepest flat — the nerve is a full simplex; the contraction attempt and its precise gap: the transferred cochains agree only on triple overlaps with J₀); (c) direct socle analysis of the deepest-flat localization (a finite computation per m in principle).

## 5. The assembled chain (what falls when the inch falls)
E = 0 at the deepest flat ⟹ S1-global ⟹ C ≅ im(ob) ⊆ ⊕_F O(F)^{m−1} with the telescope ⟹ **C is CM** ⟹ (Golden Reduction, ratified) **the Sharp Regularity Law is a theorem ∀m** ⟹ **Peaje C liquidated + e₀(k) = k² (Peaje D sharp) + the Hammock's G1** — one localized vanishing releases the entire chain. Every link except the last inch is now pencil, audited or delivered this turn.

## 6. Honest scope
Proven this turn: W1, W2, W3 (pencil, m-step inside). Verified: E ≡ 0 in four letters, all degrees. Not proven: the deepest-flat vanishing (named, three candidate mechanisms). Not completed: B₄'s ob-probe (script reproducible). Peaje A′ (Huevo 2): not reached. No shout — the golden egg is cracked to its last millimeter of shell, not yet open.

## 7. Attack surface for the Auditor
(A) W1's Young-subgroup membership for Z-flats (write the block classification explicitly — my statement generalizes the c=1 and 3-cycle computations; verify no exotic Z-flat type). (B) W2's totalization (check P's flat factors decompose as claimed — flats of a product = (flat)×(sheet) unions). (C) The ob implementation (sign conventions; ob∘φ = 0 implicitly confirmed by rank(ob) ≤ C throughout — make it an explicit gate). (D) Run B₄'s ob-probe to completion (fifth letter). (E) The three kill mechanisms of §4 — (a) is the shortest: depth Q ≥ 2 via Serre's S2 on the CI or a direct H¹_m computation.

**MARCADOR: [TANDA 4 — EL NERVIO CASI ABIERTO: E := ker(ob)/im(φ) ≡ 0 BYTE-EXACT en CUATRO letras, todos los grados (S1-global verificado instancia a instancia) · THEOREM W1: arquitectura de estrellas — todo flat tiene estrella = palabra de letras menores, y el complejo de defecto LOCALIZA · THEOREM W2: Künneth/Leibniz del complejo de defecto (la técnica de capas de Composition/Species, ahora en los tres términos) · THEOREM W3: inducción en codimensión con el paso m DENTRO — E soportado SOLO en el flat más profundo · LA ÚLTIMA PULGADA: el vanishing en el flat profundo — nombrado, con tres mecanismos candidatos (PS-acyclicity vía depth Q ≥ 2 es el más corto) · la cadena entera lista: esa pulgada ⟹ C CM ⟹ Regularidad Afilada ∀m ⟹ Peaje C + e₀=k² + G1 del Hammock DE UN GOLPE · B₄-probe incompleto (reproducible) · A′ no alcanzado · SIN GRITO: cáscara rota hasta el último milímetro]. — Bisel (Constructor, Fable), Tanda 4 — snapshot y auditoría a Cárdano**
