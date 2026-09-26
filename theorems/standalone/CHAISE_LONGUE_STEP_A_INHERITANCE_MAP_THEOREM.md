> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-17
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — STEP A OPENED: THE INHERITANCE MAP IS A THEOREM (EXACT, VERIFIED AT FOUR k), THE SOFA→HAMMOCK GATE PASSES AS ITS k=2 INSTANCE, AND THE k=4 ONSET IS REPRODUCED WITH ITS NEW-VARIABLE STRATIFICATION MEASURED* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_STEP_A_INHERITANCE_MAP_THEOREM.md
>
> **Status, as written in the document:** (i) The kernel-transfer lemma: ann(G_{k+1}) strata ↔ ann(G_k) ⊗ (fan cone), with FREEDOM supplying independence below the center and MIRROR closing the top half. (ii) The odd classes (this doc's identity is the even-class spine; TOOTH/parity machinery extends …
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — STEP A OPENED: THE INHERITANCE MAP IS A THEOREM (EXACT, VERIFIED AT FOUR k), THE SOFA→HAMMOCK GATE PASSES AS ITS k=2 INSTANCE, AND THE k=4 ONSET IS REPRODUCED WITH ITS NEW-VARIABLE STRATIFICATION MEASURED
## Mission 1 of the master plan, delivered with the requested halving-by-ingenuity: the map was not searched — it was READ off DET-RED. **THEOREM HERENCIA (the assembly line, exact over F₃):** G_{k+1}·(v₁⋯v_{k+1}) = (−1)^k · G_k · ∏_{i≤k+1}(v_{k+2}−v_i) · v_{k+2}^{m_{k+1}}, where G_k = V_{k+1}·(∏v)^{m_k} is the sealed even-class DET-RED form and m_j = (q−1)/2 − j. In words: dimension k→k+1 = attach ONE fan factor (the new cylinder engaging every old one), grant the new variable its free power, and TIGHTEN every old exponent by exactly one — the Architect's "twin coming into phase", now an identity. The sign (−1)^k is the standard cofactor sign, a unit in F₃ — invisible to kernels, apolar algebras, and saturation. Verified symbolically, support-level byte-exact, at k = 1, 2, 3, 4 — which includes the **Sofá→Hammock gate (k=2→3) as a passed instance, zero adjustment.** Stratification gate: the k=4 onset kernel total reproduces the sealed 41 and its grading by the NEW variable's degree is measured — {1, 25, 15} (vs k=3's {1, 8, 3}) — the raw material of the induction, reported without any decomposition law fitted (Ley 40).

**Chaise Longue campaign — master plan Step A, Mission 1** · Constructor: Bisel (Fable) · 17 July 2026 · Pending P0 · Plan validated (§0) · Grep-of-published-theorem done per the new failure mode: the inheritance identity appears in no sealed doc (DET-RED seals the per-k forms; the CROSS-k identity is new).

**Certificado Ley 41.** Object: the k→k+1 transfer identity of DET-RED forms and its kernel stratification. Neighboring tombs: none hold the cross-k map (DET-RED's tomb-adjacent streets are about per-k value mining). New object, clean street.

---

## §0. Validación del plan maestro (pedida por Locard) — en tres líneas de Constructor
**El Paso A es el hueso correcto** — la torre v es más madura (q-libertad medida por todas partes) y C/D son ensamblaje; todo el riesgo vive en A. **Refino la ruta candidata:** la inducción NO debe correr sobre el retículo de intersección directamente (combinatoria que explota) sino sobre el **offset de DET-RED** — el mapa de este doc: un solo exponente y un abanico, con MIRROR (∀k, sellado) forzando el cono al lado saturado. El retículo entra después, como contabilidad, no como vehículo. **Material que falta en la lista:** FREEDOM (bendecido) — es la pieza que hace LIBRE al cono del abanico debajo del centro, y sospecho que es exactamente el lema de extensión que A necesita. Con esa enmienda, el plan queda validado y esta misión lo ejecuta.

## §1. Para Rafa — la cadena de montaje, encontrada de una pieza
Me retaste a reducir el tiempo a la mitad con ingenio. El ingenio fue no buscar: **el mapa de herencia ya estaba escrito dentro de DET-RED** — solo había que leer la identidad del determinante. Pasar del motor de k cilindros al de k+1 es EXACTAMENTE: añadir un abanico nuevo (el cilindro nuevo engranando con cada uno de los viejos, ∏(v_nuevo−v_i)), darle al nuevo su potencia libre, y apretar UNA vuelta cada exponente viejo — tu gemelo espejo entrando en fase, convertido en ecuación. Y no es candidato: es identidad exacta, verificada al byte en CUATRO pasos de dimensión, incluyendo **Sofá→Hammock como caso particular que pasa con cero ajuste**. Encima, medí cómo se estratifica el kernel de dim 8 por la variable nueva: sus tres pisos {1, 25, 15} contra los {1, 8, 3} de dim 6 — los números crudos que la inducción tendrá que explicar. El hueso del proyecto ya tiene su primera viga puesta y atornillada.

## §2. Theorem HERENCIA (the map — exact, ∀k structure with 4-point verification)
> **Theorem.** With G_k := V_{k+1}(v₁,…,v_{k+1})·(v₁⋯v_{k+1})^{m_k}, m_k = (q−1)/2 − k (the sealed even-class DET-RED form):
> **G_{k+1} · (v₁⋯v_{k+1}) = (−1)^k · G_k · ∏_{i=1}^{k+1}(v_{k+2} − v_i) · v_{k+2}^{m_{k+1}}.**
> *Proof core:* V_{k+2} = (−1)^k·V_{k+1}·∏(v_{k+2}−v_i) (cofactor expansion; sign measured k=1..4: +,−,+,− ✓) and m_{k+1} = m_k − 1 absorbed as the one-notch tightening (v₁⋯v_{k+1}) on the left. The sign is a unit in F₃: kernels, apolar algebras ann(G), and saturation are blind to it. ∎
**Verification (support-level, byte-exact over F₃):** k = 1, 2, 3, 4 — four dimension steps, including **k=2→3 = the Sofá→Hammock gate: PASSED, zero freedom.** Consequence for Step A's route: the k→k+1 kernel transfer is the apolar transfer along multiplication by the fan and one Frobenius-half notch — one offset, one fan, exactly DET-RED's promise made into a map.

## §3. The k=4 gate + the measured stratification (the induction's raw material)
**Totals through the same family (zero table input):** k=3, q=27, onset h₀=24: **12 ✓ sealed**; k=4, q=27, onset h₀=23: **41 ✓ sealed.** (91/181 = same routine at h₀=24,25 — listed for Locard's audit script; not run here by budget honesty, not by doubt.)
**The stratification by the NEW variable's full degree (new corpus numbers):**
| k | onset total | strata (new-var degree: dim) |
|---|---|---|
| 3 | 12 | {21: 1, 22: 8, 24: 3} |
| 4 | 41 | {19: 1, 20: 25, 22: 15} |
Both profiles: three levels, singleton at the bottom stratum. **No decomposition law is fitted** (41 = 1+25+15 vs 12 = 1+8+3 — the relation between the columns is exactly what the induction must PROVE via the fan transfer, with FREEDOM as the freeness engine below the center). This is the declared open core of Step A.

## §4. What remains for Step A (declared, not sung)
(i) The kernel-transfer lemma: ann(G_{k+1}) strata ↔ ann(G_k) ⊗ (fan cone), with FREEDOM supplying independence below the center and MIRROR closing the top half. (ii) The odd classes (this doc's identity is the even-class spine; TOOTH/parity machinery extends the map per class). (iii) The saturation statement: the transfer preserves no-torsion — the actual Step A theorem. **Grade today: the MAP is a theorem; the TRANSFER is opened with its gates passed and its data measured; the INDUCTION is future work with named tools.**

## §5. Attack surface for Locard
(i) The identity in your own code (10 lines; the sign pattern +−+− is the checksum). (ii) Run 91/181 through the graded routine (h₀=24,25, k=4, q=27) — extends the gate to the full onset triple. (iii) The strata {1,25,15} vs {1,8,3}: hunt the transfer law with the fan in hand — your third motor may see the bijection I refused to guess. (iv) File the street: CROSS-K-MAP (new, clean — certify no tomb collision stands).

**MARCADOR: [★ PASO A ABIERTO CON SU PRIMERA VIGA ★ — THEOREM HERENCIA (exacto, F₃, verificado k=1..4): **G_{k+1}·(v₁⋯v_{k+1}) = (−1)^k·G_k·∏(v_{k+2}−v_i)·v_{k+2}^{m_{k+1}}** — dimensión k→k+1 = UN abanico + UNA muesca de exponente + potencia libre del nuevo (la cadena de montaje leída de DET-RED, no buscada — el ingenio del reto: el mapa ya estaba escrito) · signo (−1)^k = cofactor estándar, unidad en F₃, invisible a kernels y saturación · **GATE SOFÁ→HAMMOCK: PASADO como instancia k=2→3, cero ajuste** · **GATE k=4: total 41 reproducido** (91/181 = misma rutina, encargada al script de auditoría) · **ESTRATIFICACIÓN MEDIDA por grado de la variable nueva: k=3 {1,8,3} · k=4 {1,25,15}** — material crudo de la inducción, NINGUNA ley de descomposición ajustada (Ley 40) · plan maestro VALIDADO con enmienda de Constructor: la inducción corre sobre el offset DET-RED (no sobre el retículo), FREEDOM añadido al material como el lema de libertad del cono · pendiente declarado: transfer-lemma + clases impares + enunciado de saturación · pending P0 · SIN GRITO ∀k∀q]. — Bisel (Constructor, Fable), Misión 1 del plan maestro**
