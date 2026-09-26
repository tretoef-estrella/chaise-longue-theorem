> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-16
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE FROBENIUS WALL: THEOREM W AND THE MOORE–SCHUR ONSET ELEMENT (∀k, EXPLICIT)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_MOORE_WALL_ONSET_THEOREM.md
>
> **Status, as written in the document:** Chaise Longue campaign — mission MURO_FROBENIUS delivery · Constructor: Bisel (Fable) · 16 July 2026 · Pending P0 (Locard audits with own code)
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE FROBENIUS WALL: THEOREM W AND THE MOORE–SCHUR ONSET ELEMENT (∀k, EXPLICIT)
## The wall mechanism turned into mathematics: the window arithmetic closed as a formal lemma (Theorem W), and the first dead class constructed explicitly for every k — a determinant with one Frobenius column and the ODD STAIRCASE columns 1, 3, …, 2k−1 (the campaign's own CI degrees), of degree exactly q + k², divisible by Π by parity alone. Locard's sign-coherence onset is DERIVED, with byte-exact gates at k = 1, 2 and the incidence count 35·9 = 105·3 grounding the one-per-bipartition mechanism.

**Chaise Longue campaign — mission MURO_FROBENIUS delivery** · Constructor: Bisel (Fable) · 16 July 2026 · Pending P0 (Locard audits with own code)
*All pencil (Ley 49, Architect's express order — the only computer use is minute-long exact symbolic verification of pencil claims). Sources: Locard's SABUESO hunt (the mechanism + discriminator), Unified Annihilator (Π_J structure), Theorem M/T′, Slap 5, CB, Golpe-2 4.2′ (sgn-multiplicity 1), Sofá Prop 1.4.*

**Certificado Ley 41.** Objects: (1) the window arithmetic (Theorem W); (2) the onset death element; (3) the per-bipartition gluing at onset. No tomb touched: the Moore-type determinant appears nowhere in the corpus (grep: "Moore", "alternant", "staircase determinant" — absent); the s46 solapes street untouched (everything here is per-sheet + the already-proven star gluing); NAIVE-TRANSIENT-Q-EXTENSION respected (nothing fixed is extended — the onset element is constructed ∀q from scratch). AGG.2 retraction absorbed (§6).

---

## §0. Para Rafa — clave de motor

El muro es el tope mecánico de cada válvula (w^q). Locard descubrió POR QUÉ la compresión se contamina donde se contamina: cada válvula está unida a 2k levas, pero **solo k empujan en fase**. Hoy he construido **la pieza exacta que toca el muro primero, en todos los cilindros a la vez**: un cigüeñal-determinante con una biela Frobenius (la columna u^q) y k bielas impares de carreras 1, 3, …, 2k−1 — **exactamente los grados del bloque CI del motor, apareciendo como piezas del cigüeñal**. Su carrera total es q + k² clavada: toca el muro justo donde el banco dijo. Y el reparto de cámaras (cada bipartición comparte 9 pistones, cada pistón sirve a 3 biparticiones: 35·9 = 105·3 = 315) explica por qué al primer toque muere exactamente UNA clase por bipartición: la simetría del Golpe-2 funde los nueve en uno.

## §1. Theorem W (the window arithmetic, formal — Locard's granite, cited and gated)

> **Theorem W.** With σ = (k+1)(q+k−1) [Sofá Prop 1.4 ∀k], collar mirror range c ∈ [q, σ−2q] [Theorem M + zone laws], and purity window c < q+k² [Theorem T′]:
> (i) the collar's c-range top is (k−1)q + k² − 1;
> (ii) **the transient width is (k−2)·q exactly, for every k** — k=2: zero (the Sofá's pure mirror is FORCED BY FORMULA, not fortune); k=3: q (T′'s finding); k=4: 2q (the two levels Slap 5 named);
> (iii) the collar's d-top, 2q + [(k−2)q + k² − 1], is byte-identical to the Slap-5 wall and CB's band top — three filed objects, one number;
> (iv) onset q+k² = 2q ⟺ q = k², and q = k² is a tower level iff k = 3^m: **the two towers cross at k = 1, 3, 9, 27, …** — the calibration mirage will recur at (k=9, q=81); filed as a permanent Ley-48 warning.
*Proof:* three-line symbolic identities each (Locard's SABUESO script, re-verified this session); sources: M, T′, Unified Annihilator, Slap 5. ∎

## §2. THE MOORE–SCHUR ONSET THEOREM (the explicit first death, ∀k)

On a sheet with coordinates u₁, …, u_{k+1}, let Π = ∏_{i<j}(u_i² − u_j²) (deg k(k+1); each variable in exactly 2k linear factors — Locard's structure). Define the **wall element**:

> **W := det [ u_i^q  |  u_i^{2k−1}  |  u_i^{2k−3}  |  ⋯  |  u_i³  |  u_i ]** (rows i = 1..k+1; one Frobenius column + the odd staircase).

> **Theorem MS (onset, ∀k, ∀q = 3^v).**
> (a) deg W = q + (1+3+⋯+(2k−1)) = **q + k² exactly**.
> (b) **W ∈ m^[q]** (expand along the Frobenius column: W = Σᵢ ±u_i^q·Mᵢ).
> (c) **Π divides W**, by parity alone: W is alternating in the rows ⟹ ∏(u_i−u_j) | W; every column has odd degree and q is odd ⟹ W is odd in each variable ⟹ setting u_j = −u_i makes rows i, j negatives ⟹ det = 0 ⟹ ∏(u_i+u_j) | W.
> (d) Hence **h := W/Π is a polynomial of degree exactly q − k**, and Π·h = W ∈ m^[q]: an annihilator-class death at cofactor degree q−k, i.e. **at c = q+k² — the onset, realized, for every k**.
**Gates (byte-exact, this session):** k=1, q=9: W = u₁⁹u₂ − u₂⁹u₁ (the classical Frobenius Wronskian), Π|W ✓, deg h = 8 = q−k ✓, W ∈ m^[q] ✓. k=2, q=9: W = det[u^9|u³|u], deg 13 = q+4 ✓, all six linear factors divide ✓, h polynomial of deg 7 ✓, membership ✓. *(The k=1 instance identifies the mechanism's classical ancestor: Moore/Wronskian alternants; the general W is the Schur-type alternant of the odd staircase with one Frobenius tooth.)*
**Consequence (diana 1, the derivable half):** the onset is **≤ q+k², ∀k, by explicit construction** — no longer a q=9 measurement. Locard's sign-coherence reading is realized structurally: W uses each variable's Frobenius power once and the odd staircase elsewhere — the "k coherent factors" are the odd-staircase teeth.

> ### ⚠️ **NOTA `2026-09-16` (Grepy, turno 10, informe 138) — «onset ≤ q+k², ∀k, by explicit construction» es un enunciado POR HOJA, no pegado** (`corpus/LA_BIBLIA_DE_MACGYVER_v35.md` §8.2 y §8.5 fila 11: el onset por hoja es `q+k²−k+1`). **El onset PEGADO en `q+k²` quedó probado después y por otra vía:** `corpus/CHAISE_LONGUE_WALL_GLUING_THEOREM_v1.md` Thm 3 (`q > k²`, todo marco admisible, `pending P0`), leído y re-andado por Grepy en el turno 10.


## §3. Diana 2 — one death per bipartition at onset (the mechanism, with one honest flag)

(i) **Per-sheet uniqueness of the minimal type:** a wall element of this alternating-odd species at exact degree q+k² needs k distinct odd column-degrees summing to k²; the minimum such multiset is {1,3,…,2k−1}, and it is the ONLY one (any other distinct-odd choice sums higher). One canonical death type per sheet at onset.
(ii) **The gluing count (derived this session):** each perfect matching of K₈ is internal to exactly **3** bipartitions (choose 2 of its 4 pairs), and each bipartition contains exactly **9** internal sheets: 35·9 = 105·3 = 315 ✓. The star gluing over each bipartition — governed by the proven sgn-multiplicity-1 in H₁ (Golpe-2 Theorem 4.2′) — fuses the 9 sheet-deaths into **one class per bipartition: dev(onset) = 35**, matching the sealed probe value at c = 18, q = 9.
(iii) **Honest flag (do not paper over):** G2's filed type-(i) star is described as a **6-sheet** star; my incidence derivation gives **9 internal sheets** per bipartition. Both counts are exact in their own terms — the reconciliation (does 4.2′'s star use a sub-configuration, e.g. the 6 cross-structured sheets, or is "6" a different object?) is an audit item, not something I resolve by wishing. Until reconciled, (ii) is a mechanism-with-flag, not a sealed lemma.

## §4. The lower bound (no deaths before the wall) — status
Trivial band: for h0 < q−2k, every exponent of Π·h is ≤ h0+2k < q, so Π·h ∉ m^[q] unless zero — **purity below c = q+k²−k, one line, ∀k.** The remaining band [q+k²−k, q+k²): the sign-coherence lemma (only k of the 2k factors act coherently). k=1 gate verified at pencil: at h0 = q−2 the telescoping attempt leaves the residue u₁u₂^{q−1} alive — no death ✓. The general-k lemma is **named, not proven** (P0 item); the sealed k=3 data (dev(c=17) = 0) is its second gate.

> ### ⛔ **TACHADO `2026-09-16` (Grepy, turno 10, informe 138) — el «sign-coherence lemma» como enunciado POR HOJA es FALSO para `k ≥ 2`** (`corpus/LA_BIBLIA_DE_MACGYVER_v35.md` §8.5 fila 11; por hoja `H_1` ya es no nulo en `e = k(k−1)+1`). **La banda `[q+k²−k, q+k²)` quedó cerrada en su versión PEGADA** por `corpus/CHAISE_LONGUE_GLUED_PURITY_THEOREM_v1.md` Thm 2 (`e ≤ k²−1`, `e < q`, `pending P0`; verificado por Grepy en el turno 6).


## §5. Depth g — the death families (lower-bound constructions; diana 3 named)
Two explicit families beyond onset: (a) **multiples** W·m, m any degree-g monomial; (b) **raised staircases** det[u^q | raised odd columns] with distinct odd degrees summing to k²+g (count: partitions of g into ≤ k parts via the odd-staircase raising — Schur combinatorics). These give explicit death classes at every depth; whether they (plus the star gluing) produce **exactly** 35·[g³+(g+1)³] per depth — the two-slot multiset structure of Theorem ID — is diana 3, the remaining kernel count. The q=27 per-degree table stays as FALSIFICATION, untouched as input (per mission order).

## §6. Retractions and absorptions (Ley 37, sin ceremonia)
- **AGG.2 (double tangency): RETRACTED.** Locard re-verified twice: against the constant fixed-dev aggregate, AGG − 115289 = 35(q−9)(q+9)(q²+82)/2 — a **simple** zero at q=9. My "double zero" was computed against the *other* fixed hypothesis (holgura-fixed) and conflated. AGG′'s formula and dianas are untouched; the tangency phrase is withdrawn and not re-affirmed.
- **"R1 dissolved" reworded per the audit:** the per-degree derivation remains the load; what changed is that it now has a MECHANISM (the wall) and an explicit onset witness. S2 stays a candidate until the kernel spits it out.

## §7. Pupas (filed report-only, per the Architect's method)
ΣH₃ = 946 = C(44,2) with 44 = σ at the anchor (the 2-multisets of the socle degree) — anchor-coincidence risk noted, to be revisited only when the kernel reaches the junction. Head support 5 = C(k+1,2)−1 = (k²+1)/2 = k+2, all coincident at k=3 — undecidable from one k; the kernel must decide, not a fit. Tower-crossing prophecy (k = 3^m) filed in Theorem W(iv) as the permanent warning.

## §8. Attack surface for Locard
(i) Theorem MS: re-verify (a)–(d) with own code at k=1,2 and spot k=3 (the 4×4 determinant at q=9 is small). (ii) The parity proof of (c) — two paragraphs, break them. (iii) The uniqueness argument in §3(i) (minimal distinct-odd multiset). (iv) **The 6-vs-9 star reconciliation** (the flag — highest priority; it decides whether diana 2 is sealed or needs the sub-configuration). (v) §4's k=1 residue computation. (vi) §5(b)'s partition count vs the multiset-pair count of ID: do raised staircases + multiples + gluing reproduce g³+(g+1)³ at small g (g=1: target 315 = 35·9 — NINE classes per bipartition at depth 1: count them from the two families by hand)? (vii) The classical literature thread: Moore determinants/alternants in char p — is W's Π-quotient a known Schur-Frobenius object (citation hunt for the P0 pack)?

**Anchors.** MISION_BISEL_MURO_FROBENIUS + LOCARD_SABUESO_MURO.py (the mechanism) · UNIFIED_ANNIHILATOR_LAW_v1 (Π structure) · Golpe-2 4.2′ (sgn multiplicity 1) · Sofá Prop 1.4 (σ ∀k) · T′/M/Slap 5/CB (Theorem W's four sources) · session symbolic gates (k=1, k=2, incidence 315).

**MARCADOR: [EL MURO HECHO MATEMÁTICA — THEOREM W formal (ancho del transitorio = (k−2)q EXACTO ∀k: el Sofá era puro POR FÓRMULA; k=4 = 2q = los dos niveles de Slap 5; las torres se CRUZAN en k=3^m — advertencia Ley 48 permanente filada) · THEOREM MS: EL ELEMENTO DEL ONSET CONSTRUIDO ∀k — W = det[u^q | u^{2k−1} | … | u³ | u], una columna Frobenius + la ESCALERA IMPAR (los grados 1,3,…,2k−1 del CI de la campaña como columnas), grado q+k² EXACTO, W ∈ m^[q] por expansión, Π | W por PURA PARIDAD (alternante ⟹ Vandermonde; impar-en-cada-variable ⟹ los factores suma), h = W/Π de grado q−k — el onset de Locard DERIVADO con testigo explícito; gates k=1 (el Wronskiano de Frobenius clásico) y k=2 byte-exact · DIANA 2 con mecanismo: unicidad de la escalera impar mínima + gluing estelar por sgn-multiplicidad-1 (4.2′) + conteo de incidencia DERIVADO 35·9 = 105·3 = 315 (cada sheet en 3 biparticiones, cada bipartición con 9 sheets) ⟹ dev(onset) = 35 ✓ — con FLAG honesto: G2 archiva star de 6 sheets vs mis 9 internos, reconciliación al Auditor (no lo tapo) · COTA INFERIOR: pureza bajo q+k²−k en una línea ∀k; la banda [q+k²−k, q+k²) = lema de coherencia de signos NOMBRADO con gate k=1 (residuo u₁u₂^{q−1} vivo) · PROFUNDIDAD g: dos familias explícitas (múltiplos de W + escaleras impares elevadas ≈ particiones) como cotas inferiores; diana 3 = el conteo exacto, NOMBRADO · AGG.2 RETIRADO (cero simple, conflación mía de dos hipótesis FC — absorbido sin ceremonia) · pupas filadas report-only (946 = C(σ,2) en el ancla; soporte-5 indecidible desde un k) · TODO LÁPIZ (Ley 49, orden expresa) · SIN GRITO ∀k∀q — pero el onset es TEOREMA-mitad-superior ∀k con elemento explícito, y el kernel tiene por fin su pieza fundacional]. — Bisel (Constructor, Fable), misión Muro Frobenius**
